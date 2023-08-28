--[[
FiOne
Copyright (C) 2021  Rerumu

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
]]
--!strict

-- Localise to prevent env changes from breaking it

local bit = bit32
local bit_rshift = bit.rshift
local bit_band = bit.band
local bit_lshift = bit.lshift

local _table = table
local table_move = _table.move
local table_create = _table.create
local table_unpack = _table.unpack
local table_concat = _table.concat
local table_clear = _table.clear

local _select = select
local _tonumber = tonumber
local _pcall = pcall
local _tostring = tostring
local _getfenv = getfenv
local _error = error

-- Remap for better lookup
local ROP_MOVE = 3
local ROP_GETUPVAL = 2
local OPCODE_REMAP = {
	-- level 1
	[22] = 18, -- JMP
	[31] = 8, -- FORLOOP
	[33] = 28, -- TFORLOOP
	-- level 2
	[0] = ROP_MOVE, -- MOVE
	[1] = 13, -- LOADK
	[2] = 23, -- LOADBOOL
	[26] = 33, -- TEST
	-- level 3
	[12] = 1, -- ADD
	[13] = 6, -- SUB
	[14] = 10, -- MUL
	[15] = 16, -- DIV
	[16] = 20, -- MOD
	[17] = 26, -- POW
	[18] = 30, -- UNM
	[19] = 36, -- NOT
	-- level 4
	[3] = 0, -- LOADNIL
	[4] = ROP_GETUPVAL, -- GETUPVAL
	[5] = 4, -- GETGLOBAL
	[6] = 7, -- GETTABLE
	[7] = 9, -- SETGLOBAL
	[8] = 12, -- SETUPVAL
	[9] = 14, -- SETTABLE
	[10] = 17, -- NEWTABLE
	[20] = 19, -- LEN
	[21] = 22, -- CONCAT
	[23] = 24, -- EQ
	[24] = 27, -- LT
	[25] = 29, -- LE
	[27] = 32, -- TESTSET
	[32] = 34, -- FORPREP
	[34] = 37, -- SETLIST
	-- level 5
	[11] = 5, -- SELF
	[28] = 11, -- CALL
	[29] = 15, -- TAILCALL
	[30] = 21, -- RETURN
	[35] = 25, -- CLOSE
	[36] = 31, -- CLOSURE
	[37] = 35, -- VARARG
}

-- OPCODE types for getting values
local OPCODE_TYPES = {
	--[[
	Originally the starting index was 0, removed to be faster
	
	The string values have also been swapped with numbers:
		'ABC': 1
		'ABx': 2
		'AsBx': 3
	]]
	1,
	2,
	1,
	1,
	1,
	2,
	1,
	2,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	3,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	1,
	3,
	3,
	1,
	1,
	1,
	2,
	1,
}

local op_b_is_OpArgK = {
	--Index starts at 1 instead of 0
	false,
	true,
	false,
	false,
	false,
	true,
	false,
	true,
	false,
	true,
	false,
	false,
	true,
	true,
	true,
	true,
	true,
	true,
	false,
	false,
	false,
	false,
	false,
	true,
	true,
	true,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
}

local op_c_is_OpArgK = {
	--Index starts at 1 instead of 0
	false,
	false,
	false,
	false,
	false,
	false,
	true,
	false,
	false,
	true,
	false,
	true,
	true,
	true,
	true,
	true,
	true,
	true,
	false,
	false,
	false,
	false,
	false,
	true,
	true,
	true,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
	false,
}

type const_list = {(boolean | string | number)?}

type lines = {number}

type uv = {
	index: any,
	value: any,
	store: any
}

type data = {
	value: number,
	A: any,
	op: number,

	is_KB: boolean?,
	is_KC: boolean?,
	const: any,
	B: any,
	C: any,
	Bx: any,
	is_K: boolean?,
	sBx: any,
	const_B: any,
	const_C: any,
}

type code = {data}

type proto = {
	source: string,
	num_upval: number,
	num_param: number,
	max_stack: number,
	code: code,
	const: const_list,
	subs: {proto},
	lines: lines
}

-- int rd_int_basic(string src, int s, int e, int d)
-- @src - Source binary string
-- @s - Start index of a little endian integer
-- @e - End index of the integer
-- @d - Direction of the loop
local function rd_int_basic(src: string, s: number, e: number, d: number): number
	local num = 0

	-- if bb[l] > 127 then -- signed negative
	-- 	num = num - 256 ^ l
	-- 	bb[l] = bb[l] - 128
	-- end

	local power = 1
	for i = s, e, d do
		num = num + power * src:byte(i, i)
		power = power * 256
	end

	return num
end

-- float rd_flt_basic(byte f1..8)
-- @f1..4 - The 4 bytes composing a little endian float
local function rd_flt_basic(f1: number, f2: number, f3: number, f4: number): number
	local sign = (-1) ^ bit_rshift(f4, 7)
	local exp = bit_rshift(f3, 7) + bit_lshift(bit_band(f4, 0x7F), 1)
	local frac = f1 + bit_lshift(f2, 8) + bit_lshift(bit_band(f3, 0x7F), 16)
	local normal = 1

	if exp == 0 then
		if frac == 0 then
			return sign * 0
		else
			normal = 0
			exp = 1
		end
	elseif exp == 0x7F then
		if frac == 0 then
			return sign * (1 / 0)
		else
			return sign * (0 / 0)
		end
	end

	return sign * 2 ^ (exp - 127) * (1 + normal / 2 ^ 23)
end

-- double rd_dbl_basic(byte f1..8)
-- @f1..8 - The 8 bytes composing a little endian double
local function rd_dbl_basic(f1: number, f2: number, f3: number, f4: number, f5: number, f6: number, f7: number, f8: number)
	local sign = (-1) ^ bit_rshift(f8, 7)
	local exp = bit_lshift(bit_band(f8, 0x7F), 4) + bit_rshift(f7, 4)
	local frac = bit_band(f7, 0x0F) * 2 ^ 48
	local normal = 1

	local frac = frac + (f6 * 2 ^ 40) + (f5 * 2 ^ 32) + (f4 * 2 ^ 24) + (f3 * 2 ^ 16) + (f2 * 2 ^ 8) + f1 -- help

	if exp == 0 then
		if frac == 0 then
			return sign * 0
		else
			normal = 0
			exp = 1
		end
	elseif exp == 0x7FF then
		if frac == 0 then
			return sign * (1 / 0)
		else
			return sign * (0 / 0)
		end
	end

	return sign * 2 ^ (exp - 1023) * (normal + frac / 2 ^ 52)
end

-- int rd_int_le(string src, int s, int e)
-- @src - Source binary string
-- @s - Start index of a little endian integer
-- @e - End index of the integer

local function rd_int_le(src: string, s: number, e: number) return rd_int_basic(src, s, e - 1, 1) end

-- int rd_int_be(string src, int s, int e)
-- @src - Source binary string
-- @s - Start index of a big endian integer
-- @e - End index of the integer
local function rd_int_be(src: string, s: number, e: number) return rd_int_basic(src, e - 1, s, -1) end

local function stm_lua_func(
	s_index: number,
	s_source: string,

	psrc: string): (proto, number)

	-- header flags
	local little, size_int, size_szt, size_ins, size_num, flag_int = s_source:byte(7, 12)
	local little = little ~= 0

	local rdr_func: (string, number, number) -> (number) = if little then rd_int_le else rd_int_be

	local proto_source
	-- source is propagated
	local pos = s_index + size_szt
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	if len ~= 0 then
		local index = s_index
		local pos = index + len

		s_index = pos

		proto_source = s_source:sub(index, pos - 2)
	else
		proto_source = psrc
	end

	s_index = s_index + size_int -- line defined
	s_index = s_index + size_int -- last line defined

	local proto_num_upval, proto_num_param = s_source:byte(s_index, s_index + 1)
	local proto_max_stack = s_source:byte(s_index + 3, s_index + 3)
	s_index = s_index + 4 -- proto_max_stack, finish

	--stm_inst_list
	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos

	local proto_code: code = table_create(len)

	for i = 1, len do
		local pos = s_index + size_ins
		local ins = rdr_func(s_source, s_index, pos)
		s_index = pos

		local op = bit_band(ins, 0x3F)
		local args = OPCODE_TYPES[op + 1]
		local data: data = {
			value = ins,
			op = OPCODE_REMAP[op],
			A = bit_band(bit_rshift(ins, 6), 0xFF),

			is_KB = nil,
			is_KC = nil,
			const = nil,
			B = nil,
			C = nil,
			Bx = nil,
			is_K = nil,
			sBx = nil,
			const_B = nil,
			const_C = nil
		}

		if args == 1 then
			local B: any = bit_band(bit_rshift(ins, 23), 0x1FF)
			local C: any = bit_band(bit_rshift(ins, 14), 0x1FF)

			data.is_KB = op_b_is_OpArgK[op + 1] and B > 0xFF -- post process optimization
			data.is_KC = op_c_is_OpArgK[op + 1] and C > 0xFF

			if op == 10 then -- decode NEWTABLE array size, store it as constant value
				local e = bit_band(bit_rshift(B, 3), 31)
				if e == 0 then
					data.const = B
				else
					data.const = bit_lshift(bit_band(B, 7) + 8, e - 1)
				end
			elseif op == 2 then -- precompute LOADBOOL `~= 0` operations
				B = B ~= 0
				if C ~= 0 then
					C = 1
				end
			elseif 
				op == 23 or -- EQ
				op == 24 or -- LT
				op == 25 -- LE
			then -- precompute `~= 0` operations
				data.A = data.A ~= 0
			elseif
				op == 26 or -- TEST
				op == 27 -- TESTSET
			then -- precompute `~= 0` operations
				C = C ~= 0
			end

			data.B = B
			data.C = C
		elseif args == 2 then
			data.Bx = bit_band(bit_rshift(ins, 14), 0x3FFFF)
			data.is_K = op_b_is_OpArgK[op + 1]
		else--if args == 3 then

			--args must be 3, there's no other value...
			data.sBx = bit_band(bit_rshift(ins, 14), 0x3FFFF) - 131071
		end

		proto_code[i] = data
	end

	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	local proto_const: {any} = table_create(len)

	for i = 1, len do
		local tt = s_source:byte(s_index, s_index)
		s_index += 1

		if tt == 1 then
			local bt = s_source:byte(s_index + 1, s_index + 1)
			s_index += 1

			proto_const[i] = bt ~= 0
		elseif tt == 3 then
			if flag_int ~= 0 then
				local pos = s_index + size_num
				proto_const[i] = rdr_func(s_source, s_index, pos)
				s_index = pos
			else
				if size_num == 4 then
					--4 bytes, float

					-- fn cst_flt_rdr(string src, int len, fn func)
					-- @len - Length of type for reader
					-- @func - Reader callback

					if little then
						proto_const[i] = rd_flt_basic(s_source:byte(s_index, s_index + 3))

						s_index = s_index + size_num
					else
						--rd_flt_be
						local f1, f2, f3, f4 = s_source:byte(s_index, s_index + 3)
						local flt = rd_flt_basic(f4, f3, f2, f1)

						s_index = s_index + size_num

						proto_const[i] = flt
						--big
					end
				elseif size_num == 8 then
					--8 bytes, double

					if little then
						proto_const[i] = rd_dbl_basic(s_source:byte(s_index, s_index + 7))
						s_index = s_index + size_num
					else
						local f1, f2, f3, f4, f5, f6, f7, f8 = s_source:byte(s_index, s_index + 7) -- same
						proto_const[i] = rd_dbl_basic(f8, f7, f6, f5, f4, f3, f2, f1)

						s_index = s_index + size_num
						--big
					end
				else
					_error('unsupported float size')
				end
			end
		elseif tt == 4 then
			local pos = s_index + size_szt
			local len = rdr_func(s_source, s_index, pos)
			s_index = pos

			if len ~= 0 then
				local index = s_index
				local pos = index + len

				s_index = pos

				proto_const[i] = s_source:sub(index, pos - 2)
			else
				proto_const[i] = nil
			end
		else
			proto_const[i] = nil
		end
	end

	--stm_sub_list
	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	local proto_subs = table_create(len)
	for i = 1, len do
		local proto_sub, new_s_index = stm_lua_func(
			s_index,
			s_source,

			proto_source
		)

		s_index = new_s_index
		proto_subs[i] = proto_sub -- offset +1 in CLOSURE
	end

	--stm_line_list
	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	local proto_lines = table_create(len)
	for i = 1, len do
		local pos = s_index + size_int
		proto_lines[i] = rdr_func(s_source, s_index, pos)
		s_index = pos
	end

	--stm_loc_list
	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	for i = 1, len do
		local pos = s_index + size_szt
		local len = rdr_func(s_source, s_index, pos)
		s_index = pos
		s_index = s_index + len

		s_index = s_index + size_int
		s_index = s_index + size_int
	end

	--stm_upval_list
	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	for i = 1, len do
		local pos = s_index + size_szt
		local len = rdr_func(s_source, s_index, pos)
		s_index = pos

		s_index = s_index + len
	end

	-- post process optimization
	for _, v in proto_code do
		if v.is_K then
			v.const = proto_const[v.Bx + 1] -- offset for 1 based index
		else
			if v.is_KB then v.const_B = proto_const[v.B - 255] end

			if v.is_KC then v.const_C = proto_const[v.C - 255] end
		end
	end

	return {
		source = proto_source,
		num_upval = proto_num_upval,
		num_param = proto_num_param,
		max_stack = proto_max_stack,
		code = proto_code,
		const = proto_const,
		subs = proto_subs,
		lines = proto_lines
	}, s_index
end

local function lua_bc_to_state(src: string): proto
	-- stream object
	if src:sub(1, 4) ~= '\27Lua' then _error('invalid Lua signature') end
	local luaVersion, luaFormat = src:byte(5, 6)
	if luaVersion ~= 0x51 then _error('invalid Lua version') end
	if luaFormat ~= 0 then _error('invalid Lua format') end

	return stm_lua_func(
		13,
		src,

		'@virtual'
	)
end

local function lua_wrap_state(proto: proto, upvals: {uv}?)
	local proto_max_stack = proto.max_stack
	local proto_num_param = proto.num_param
	local proto_code = proto.code
	local proto_subs = proto.subs

	local pc = 1
	local function handleErrors(success, ...)
		if success then
			return ...
		else
			_error(proto.source..":"..proto.lines[pc - 1]..": "..( ... or "Error occurred, no output from Lua." ), 0)
		end
	end

	local memory = table_create(proto_max_stack - 1)

	local top_index = -1
	local function call(function_register: number, C: number, ...)
		local ret_count
		if C == 0 then
			ret_count = _select("#", ...)
			top_index = function_register + ret_count - 1
		else
			ret_count = C - 1
		end

		for i = 1, ret_count do
			memory[function_register + i - 1] = _select(i, ...)
		end
	end

	local vararg_len
	local vararg_list

	local function run()
		top_index = -1
		local open_list: {uv} = {}

		while true do
			local inst = proto_code[pc]
			local op = inst.op
			pc = pc + 1

			if op < 18 then
				if op < 8 then
					if op < 3 then
						if op < 1 then
							--[[LOADNIL]]
							for i = inst.A, inst.B do memory[i] = nil end
						elseif op > 1 then
							--[[GETUPVAL]]
							local uv = (upvals:: {uv})[inst.B]

							memory[inst.A] = uv.store[uv.index]
						else
							--[[ADD]]

							memory[inst.A] =
								(if inst.is_KB then inst.const_B else memory[inst.B]) -- left
								+
								(if inst.is_KC then inst.const_C else memory[inst.C]) -- right
						end
					elseif op > 3 then
						if op < 6 then
							if op > 4 then
								--[[SELF]]
								local memory_B = memory[inst.B]

								local A = inst.A
								memory[A + 1] = memory_B
								memory[A] = memory_B[if inst.is_KC then inst.const_C else memory[inst.C]]
							else
								--[[GETGLOBAL]]
								memory[inst.A] = _getfenv()[inst.const]
							end
						elseif op > 6 then
							--[[GETTABLE]]
							memory[inst.A] = memory[inst.B][if inst.is_KC then inst.const_C else memory[inst.C]]
						else
							--[[SUB]]
							memory[inst.A] = 
								(if inst.is_KB then inst.const_B else memory[inst.B]) -- left
							-
								(if inst.is_KC then inst.const_C else memory[inst.C]) -- right
						end
					else --[[MOVE]]
						memory[inst.A] = memory[inst.B]
					end
				elseif op > 8 then
					if op < 13 then
						if op < 10 then
							--[[SETGLOBAL]]
							_getfenv()[inst.const] = memory[inst.A]
						elseif op > 10 then
							if op < 12 then
								--[[CALL]]
								local function_register = inst.A
								local B = inst.B

								call(function_register, inst.C,
									memory[function_register](
										table_unpack(memory, function_register + 1, function_register + 
											if B == 0 then top_index - function_register else B - 1 -- param_count
										)
									)
								)
							else
								--[[SETUPVAL]]
								local uv = (upvals:: {uv})[inst.B]

								uv.store[uv.index] = memory[inst.A]
							end
						else
							--[[MUL]]
							memory[inst.A] = 
								(if inst.is_KB then inst.const_B else memory[inst.B]) -- left
								*
								(if inst.is_KC then inst.const_C else memory[inst.C]) -- right
						end
					elseif op > 13 then
						if op < 16 then
							if op > 14 then
								--[[TAILCALL]]
								local A = inst.A
								local B = inst.B
								local params = if B == 0 then top_index - A else B - 1

								for i, uv in open_list do
									local uv_index = uv.index
									if uv_index >= 0 then
										uv.value = uv.store[uv_index] -- store value
										uv.store = uv
										uv.index = 'value' -- self reference
										open_list[i] = nil
									end
								end

								return memory[A](table_unpack(memory, A + 1, A + params))
							else
								--[[SETTABLE]]
								memory[inst.A]
								[if inst.is_KB then inst.const_B else memory[inst.B]] -- index
									= if inst.is_KC then inst.const_C else memory[inst.C] -- value
							end
						elseif op > 16 then
							--[[NEWTABLE]]
							memory[inst.A] = table_create(inst.const)
						else
							--[[DIV]]
							memory[inst.A] = 
								(if inst.is_KB then inst.const_B else memory[inst.B]) -- left
								/
								(if inst.is_KC then inst.const_C else memory[inst.C]) -- right
						end
					else
						--[[LOADK]]
						memory[inst.A] = inst.const
					end
				else
					--[[FORLOOP]]
					local A = inst.A
					local step = memory[A + 2]
					local index = memory[A] + step

					if step >= 0 then
						if index <= memory[A + 1] then
							memory[A] = index
							memory[A + 3] = index
							pc = pc + inst.sBx
						end
					elseif index >= memory[A + 1] then
						memory[A] = index
						memory[A + 3] = index
						pc = pc + inst.sBx
					end
				end
			elseif op > 18 then
				if op < 28 then
					if op < 23 then
						if op < 20 then
							--[[LEN]]
							memory[inst.A] = #memory[inst.B]
						elseif op > 20 then
							if op < 22 then
								--[[RETURN]]
								local A = inst.A
								local B = inst.B
								local len = if B == 0 then top_index - A + 1 else B - 1

								for i, uv in open_list do
									local uv_index = uv.index
									if uv_index >= 0 then
										uv.value = uv.store[uv_index] -- store value
										uv.store = uv
										uv.index = 'value' -- self reference
										open_list[i] = nil
									end
								end

								return table_unpack(memory, A, A + len - 1)
							else
								--[[CONCAT]]
								memory[inst.A] = table_concat(memory, "", inst.B, inst.C)
							end
						else
							--[[MOD]]
							memory[inst.A] = 
								(if inst.is_KB then inst.const_B else memory[inst.B]) -- left
								%
								(if inst.is_KC then inst.const_C else memory[inst.C]) -- right
						end
					elseif op > 23 then
						if op < 26 then
							if op > 24 then
								--[[CLOSE]]

								local A = inst.A 
								for i, uv in open_list do
									local uv_index = uv.index
									if uv_index >= A then
										uv.value = uv.store[uv_index] -- store value
										uv.store = uv
										uv.index = 'value' -- self reference
										open_list[i] = nil
									end
								end
							else
								--[[EQ]]

								if ((if inst.is_KB then inst.const_B else memory[inst.B]) == (if inst.is_KC then inst.const_C else memory[inst.C])) == (inst.A)
								then pc = pc + proto_code[pc].sBx end

								pc = pc + 1
							end
						elseif op > 26 then
							--[[LT]]
							if ((if inst.is_KB then inst.const_B else memory[inst.B]) <
								(if inst.is_KC then inst.const_C else memory[inst.C])) == (inst.A)
							then pc = pc + proto_code[pc].sBx end

							pc = pc + 1
						else
							--[[POW]]
							memory[inst.A] = 
								(if inst.is_KB then inst.const_B else memory[inst.B])
								^
								(if inst.is_KC then inst.const_C else memory[inst.C])
						end
					else
						--[[LOADBOOL]]
						memory[inst.A] = inst.B

						pc = pc + inst.C
					end
				elseif op > 28 then
					if op < 33 then
						if op < 30 then
							--[[LE]]
							if ((if inst.is_KB then inst.const_B else memory[inst.B]) <=
								(if inst.is_KC then inst.const_C else memory[inst.C])) == (inst.A)
							then pc = pc + proto_code[pc].sBx end

							pc = pc + 1
						elseif op > 30 then
							if op < 32 then
								--[[CLOSURE]]
								local sub = proto_subs[inst.Bx + 1] -- offset for 1 based index
								local nups = sub.num_upval

								if nups ~= 0 then
									local uvlist = {}

									for i = 0, nups - 1 do
										local pseudo = proto_code[pc + i]
										local psuedo_op = pseudo.op

										if psuedo_op == ROP_MOVE then
											--open_lua_upvalue
											local index = pseudo.B
											local prev = open_list[index]

											if prev then
												uvlist[i] = prev
											else
												local prev = {index = index, store = memory, value = nil}
												open_list[index] = prev
												uvlist[i] = prev
											end
										elseif psuedo_op == ROP_GETUPVAL then
											uvlist[i] = (upvals:: {uv})[pseudo.B]
										end
									end

									pc = pc + nups

									memory[inst.A] = lua_wrap_state(sub, uvlist)
								else
									memory[inst.A] = lua_wrap_state(sub, nil)
								end
							else
								--[[TESTSET]]
								local memory_B = memory[inst.B]
								if (not memory_B) ~= (inst.C) then
									memory[inst.A] = memory_B
									pc = pc + proto_code[pc].sBx
								end
								pc = pc + 1
							end
						else
							--[[UNM]]
							memory[inst.A] = -memory[inst.B]
						end
					elseif op > 33 then
						if op < 36 then
							if op > 34 then
								--[[VARARG]]
								local A = inst.A
								local len = inst.B

								if len == 0 then
									len = vararg_len
									top_index = A + len - 1
								end

								table_move(vararg_list, 1, len, A, memory)
							else
								--[[FORPREP]]
								local A = inst.A

								local init = _tonumber(memory[A])
								if init then
									local limit = _tonumber(memory[A + 1])
									if limit then
										local step = _tonumber(memory[A + 2])
										if step then
											memory[A] = init - step
											memory[A + 1] = limit
											memory[A + 2] = step
										else
											_error('`for` step must be a number')
										end
									else
										_error('`for` limit must be a number')
									end
								else
									_error('`for` initial value must be a number')
								end

								pc = pc + inst.sBx
							end
						elseif op > 36 then
							--[[SETLIST]]
							local A = inst.A

							local len = inst.B
							if len == 0 then len = top_index - A end

							local C = inst.C
							if C == 0 then
								C = inst[pc].value
								pc = pc + 1
							end

							table_move(
								memory,
								A + 1,
								A + len,
								((C - 1) * 50) + 1, -- FIELDS_PER_FLUSH = 50
								memory[A]
							)
						else
							--[[NOT]]
							memory[inst.A] = not memory[inst.B]
						end
					else
						--[[TEST]]
						if (not memory[inst.A]) ~= (inst.C) then pc = pc + proto_code[pc].sBx end
						pc = pc + 1
					end
				else
					--[[TFORLOOP]]
					local A = inst.A

					local vals = {memory[A](memory[A + 1], memory[A + 2])}

					-- base is A + 3

					table_move(vals, 1, inst.C, A + 3, memory)

					local memory_base = memory[A + 3]
					if memory_base ~= nil then
						memory[A + 2] = memory_base
						pc = pc + proto_code[pc].sBx
					end

					pc = pc + 1
				end
			else
				--[[JMP]]
				pc = pc + inst.sBx
			end
		end
	end

	return function(...)
		local passed = {...}

		table_clear(memory)
		table_move(passed, 1, proto_num_param, 0, memory)

		local passed_n = _select("#", ...)
		if proto_num_param < passed_n then
			vararg_len = passed_n - proto_num_param

			vararg_list = table_create(vararg_len - 1)
			table_move(passed, proto_num_param + 1, proto_num_param + 1 + vararg_len - 1, 1, vararg_list)
		else
			vararg_len = 0
			vararg_list = {}
		end

		pc = 1
		return handleErrors(_pcall(run))
	end
end

return function(bCode: string)
	return lua_wrap_state(lua_bc_to_state(bCode), nil)
end