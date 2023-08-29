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
	-- Index starts at 1 instead of 0
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
	-- Index starts at 1 instead of 0
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

type const_list = { (boolean | string | number)? }

type lines = { number }

type uv = {
	index: any,
	value: any,
	store: any,
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

type code = { data }

type proto = {
	source: string,
	num_upval: number,
	num_param: number,
	max_stack: number,
	code: code,
	const: const_list,
	subs: { proto },
	lines: lines,
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
local function rd_dbl_basic(
	f1: number,
	f2: number,
	f3: number,
	f4: number,
	f5: number,
	f6: number,
	f7: number,
	f8: number
)
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

local function rd_int_le(src: string, s: number, e: number)
	return rd_int_basic(src, s, e - 1, 1)
end

-- int rd_int_be(string src, int s, int e)
-- @src - Source binary string
-- @s - Start index of a big endian integer
-- @e - End index of the integer
local function rd_int_be(src: string, s: number, e: number)
	return rd_int_basic(src, e - 1, s, -1)
end

local function stm_lua_func(s_index: number, s_source: string, psrc: string): (proto, number)
	-- header flags
	local little, size_int, size_szt, size_ins, size_num, flag_int = s_source:byte(7, 12)
	local little = little ~= 0

	local rdr_func: (string, number, number) -> number = if little then rd_int_le else rd_int_be

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
			A = bit_band(bit_rshift(ins, 6), 0xFF),
			op = op,

			is_KB = nil,
			is_KC = nil,
			const = nil,
			B = nil,
			C = nil,
			Bx = nil,
			is_K = nil,
			sBx = nil,
			const_B = nil,
			const_C = nil,
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
				op == 23 -- EQ
				or op == 24 -- LT
				or op == 25 -- LE
			then -- precompute `~= 0` operations
				data.A = data.A ~= 0
			elseif
				op == 26 -- TEST
				or op == 27 -- TESTSET
			then -- precompute `~= 0` operations
				C = C ~= 0
			end

			data.B = B
			data.C = C
		elseif args == 2 then
			data.Bx = bit_band(bit_rshift(ins, 14), 0x3FFFF)
			data.is_K = op_b_is_OpArgK[op + 1]
		else --if args == 3 then
			--args must be 3, there's no other value...
			data.sBx = bit_band(bit_rshift(ins, 14), 0x3FFFF) - 131071
		end

		proto_code[i] = data
	end

	local pos = s_index + size_int
	local len = rdr_func(s_source, s_index, pos)
	s_index = pos
	local proto_const: { any } = table_create(len)

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
					_error("unsupported float size")
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
		local proto_sub, new_s_index = stm_lua_func(s_index, s_source, proto_source)

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
			if v.is_KB then
				v.const_B = proto_const[v.B - 255]
			end

			if v.is_KC then
				v.const_C = proto_const[v.C - 255]
			end
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
		lines = proto_lines,
	},
		s_index
end

local function lua_bc_to_state(src: string): proto
	-- stream object
	if src:sub(1, 4) ~= "\27Lua" then
		_error("invalid Lua signature")
	end
	local luaVersion, luaFormat = src:byte(5, 6)
	if luaVersion ~= 0x51 then
		_error("invalid Lua version")
	end
	if luaFormat ~= 0 then
		_error("invalid Lua format")
	end

	return stm_lua_func(13, src, "@virtual")
end

local function lua_wrap_state(proto: proto, upvals: { uv }?)
	local memory: { any } = table_create(proto.max_stack - 1)

	local top_index = -1

	local vararg_len
	local vararg_list

	local pc: number

	local open_list: { uv } = {}

	local proto_subs = proto.subs
	local proto_code = proto.code
	local compiled: { any } = table_create(#proto_code)

	local function add_1_to_pc()
		pc = pc + 1
	end
	for inst_pc, inst in proto_code do
		local op = inst.op

		-- level 1
		if op == 22 then
			-- JMP
			local inst_sBx = inst.sBx
			local jump = inst_pc + 1 + inst_sBx
			compiled[inst_pc] = function()
				pc = jump
			end
		elseif op == 31 then
			-- FORLOOP
			local inst_A = inst.A
			local inst_sBx = inst.sBx

			local finished_pc = inst_pc + 1 + inst_sBx
			local inst_A_plus_1 = inst_A + 1
			local inst_A_plus_2 = inst_A + 2
			local inst_A_plus_3 = inst_A + 3
			compiled[inst_pc] = function()
				local step = memory[inst_A_plus_2]
				local index = memory[inst_A] + step

				if step >= 0 then
					if index <= memory[inst_A_plus_1] then
						memory[inst_A] = index
						memory[inst_A_plus_3] = index
						pc = finished_pc
					end
				elseif index >= memory[inst_A_plus_1] then
					memory[inst_A] = index
					memory[inst_A_plus_3] = index
					pc = finished_pc
				end
			end
		elseif op == 33 then
			-- TFORLOOP
			local inst_A = inst.A
			local inst_C = inst.C

			local inst_A_plus_1 = inst_A + 1
			local inst_A_plus_2 = inst_A + 2
			local inst_A_plus_3 = inst_A + 3
			local pc_after_sBx = inst_pc + 1 + proto_code[inst_pc + 1].sBx
			compiled[inst_pc] = function()
				table_move(
					{ memory[inst_A](memory[inst_A_plus_1], memory[inst_A_plus_2]) },
					1,
					inst_C,
					inst_A_plus_3,
					memory
				)

				local memory_base = memory[inst_A_plus_3]
				if memory_base ~= nil then
					memory[inst_A_plus_2] = memory_base
					pc = pc_after_sBx
				end

				pc = pc + 1
			end
			-- level 2
		elseif op == 0 then
			-- MOVE
			local inst_A = inst.A
			local inst_B = inst.B

			compiled[inst_pc] = function()
				memory[inst_A] = memory[inst_B]
			end
		elseif op == 1 then
			-- LOADK
			local inst_A = inst.A
			local inst_const = inst.const

			compiled[inst_pc] = function()
				memory[inst_A] = inst_const
			end
		elseif op == 2 then
			-- LOADBOOL
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C

			local finished_pc = inst_pc + inst_C + 1
			compiled[inst_pc] = function()
				memory[inst_A] = inst_B

				pc = finished_pc
			end
		elseif op == 26 then
			-- TEST
			local inst_A = inst.A
			local inst_C = inst.C

			local pc_after_sBx = inst_pc + 1 + proto_code[inst_pc + 1].sBx
			compiled[inst_pc] = function()
				if (not memory[inst_A]) ~= inst_C then
					pc = pc_after_sBx
				end
				pc = pc + 1
			end
			-- level 3
		elseif op == 12 then
			-- ADD
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					local why_was_this_not_constant_folded = inst_const_B + inst_const_C
					compiled[inst_pc] = function()
						memory[inst_A] = why_was_this_not_constant_folded
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = inst_const_B + memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] + inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] + memory[inst_C]
					end
				end
			end
		elseif op == 13 then
			-- SUB
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					local why_was_this_not_constant_folded = inst_const_B - inst_const_C
					compiled[inst_pc] = function()
						memory[inst_A] = why_was_this_not_constant_folded
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = inst_const_B - memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] - inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] - memory[inst_C]
					end
				end
			end
		elseif op == 14 then
			-- MUL
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					local why_was_this_not_constant_folded = inst_const_B * inst_const_C
					compiled[inst_pc] = function()
						memory[inst_A] = why_was_this_not_constant_folded
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = inst_const_B * memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] * inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] * memory[inst_C]
					end
				end
			end
		elseif op == 15 then
			-- DIV
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					local why_was_this_not_constant_folded = inst_const_B / inst_const_C
					compiled[inst_pc] = function()
						memory[inst_A] = why_was_this_not_constant_folded
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = inst_const_B / memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] / inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] / memory[inst_C]
					end
				end
			end
		elseif op == 16 then
			-- MOD
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					local why_was_this_not_constant_folded = inst_const_B % inst_const_C
					compiled[inst_pc] = function()
						memory[inst_A] = why_was_this_not_constant_folded
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = inst_const_B % memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] % inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] % memory[inst_C]
					end
				end
			end
		elseif op == 17 then
			-- POW
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					local why_was_this_not_constant_folded = inst_const_B ^ inst_const_C
					compiled[inst_pc] = function()
						memory[inst_A] = why_was_this_not_constant_folded
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = inst_const_B ^ memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] ^ inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A] = memory[inst_B] ^ memory[inst_C]
					end
				end
			end
		elseif op == 18 then
			-- UNM
			local inst_A = inst.A
			local inst_B = inst.B
			compiled[inst_pc] = function()
				memory[inst_A] = -memory[inst_B]
			end
		elseif op == 19 then
			-- NOT
			local inst_A = inst.A
			local inst_B = inst.B
			compiled[inst_pc] = function()
				memory[inst_A] = not memory[inst_B]
			end
			-- level 4
		elseif op == 3 then
			-- LOADNIL
			local inst_A = inst.A
			local inst_B = inst.B
			compiled[inst_pc] = function()
				for i = inst_A, inst_B do
					memory[i] = nil
				end
			end
		elseif op == 4 then
			-- GETUPVAL
			local inst_A = inst.A
			local inst_B = inst.B
			compiled[inst_pc] = function()
				local uv = (upvals :: { uv })[inst_B]

				memory[inst_A] = uv.store[uv.index]
			end
		elseif op == 5 then
			-- GETGLOBAL
			local inst_A = inst.A
			local inst_const = inst.const

			if inst_const == "table" then
				compiled[inst_pc] = function()
					memory[inst_A] = table
				end
			elseif inst_const == "string" then
				compiled[inst_pc] = function()
					memory[inst_A] = string
				end
			elseif inst_const == "math" then
				compiled[inst_pc] = function()
					memory[inst_A] = math
				end
			elseif inst_const == "pairs" then
				compiled[inst_pc] = function()
					memory[inst_A] = pairs
				end
			elseif inst_const == "ipairs" then
				compiled[inst_pc] = function()
					memory[inst_A] = ipairs
				end
			elseif inst_const == "next" then
				compiled[inst_pc] = function()
					memory[inst_A] = next
				end
			elseif inst_const == "tostring" then
				compiled[inst_pc] = function()
					memory[inst_A] = tostring
				end
			elseif inst_const == "bit32" then
				compiled[inst_pc] = function()
					memory[inst_A] = bit32
				end
			elseif inst_const == "setmetatable" then
				compiled[inst_pc] = function()
					memory[inst_A] = setmetatable
				end
			elseif inst_const == "assert" then
				compiled[inst_pc] = function()
					memory[inst_A] = assert
				end
			elseif inst_const == "tonumber" then
				compiled[inst_pc] = function()
					memory[inst_A] = tonumber
				end
			elseif inst_const == "os" then
				compiled[inst_pc] = function()
					memory[inst_A] = os
				end
			elseif inst_const == "print" then
				compiled[inst_pc] = function()
					memory[inst_A] = print
				end
			else
				compiled[inst_pc] = function()
					memory[inst_A] = _getfenv()[inst_const]
				end
			end
		elseif op == 6 then
			-- GETTABLE
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_is_KC = inst.is_KC

			if inst_is_KC then
				compiled[inst_pc] = function()
					memory[inst_A] = memory[inst_B][inst_const_C]
				end
			else
				compiled[inst_pc] = function()
					memory[inst_A] = memory[inst_B][memory[inst_C]]
				end
			end
		elseif op == 7 then
			-- SETGLOBAL
			local inst_A = inst.A
			local inst_const = inst.const
			compiled[inst_pc] = function()
				_getfenv()[inst_const] = memory[inst_A]
			end
		elseif op == 8 then
			-- SETUPVAL
			local inst_A = inst.A
			local inst_B = inst.B
			compiled[inst_pc] = function()
				local uv = (upvals :: { uv })[inst_B]

				uv.store[uv.index] = memory[inst_A]
			end
		elseif op == 9 then
			-- SETTABLE
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB

			if inst_is_KB then
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A][inst_const_B] = inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A][inst_const_B] = memory[inst_C]
					end
				end
			else
				if inst_is_KC then
					compiled[inst_pc] = function()
						memory[inst_A][memory[inst_B]] = inst_const_C
					end
				else
					compiled[inst_pc] = function()
						memory[inst_A][memory[inst_B]] = memory[inst_C]
					end
				end
			end
		elseif op == 10 then
			-- NEWTABLE
			local inst_A = inst.A
			local inst_const = inst.const
			compiled[inst_pc] = function()
				memory[inst_A] = table_create(inst_const)
			end
		elseif op == 20 then
			-- LEN
			local inst_A = inst.A
			local inst_B = inst.B
			compiled[inst_pc] = function()
				memory[inst_A] = #memory[inst_B]
			end
		elseif op == 21 then
			-- CONCAT
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			compiled[inst_pc] = function()
				memory[inst_A] = table_concat(memory, "", inst_B, inst_C)
			end
		elseif op == 23 then
			-- EQ
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB
			local sBx = proto_code[inst_pc + 1].sBx

			if inst_is_KB then
				if inst_is_KC then
					if (inst_const_B == inst_const_C) == inst_A then
						compiled[inst_pc] = function()
							pc = pc + sBx + 1
						end
					else
						compiled[inst_pc] = add_1_to_pc
					end
				else
					local pc_after_sBx = inst_pc + 1 + sBx
					if inst_A then
						compiled[inst_pc] = function()
							if inst_const_B == memory[inst_C] then
								pc = pc_after_sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if inst_const_B ~= memory[inst_C] then
								pc = pc_after_sBx
							end
							pc = pc + 1
						end
					end
				end
			else
				if inst_is_KC then
					if inst_A then
						compiled[inst_pc] = function()
							if memory[inst_B] == inst_const_C then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if memory[inst_B] ~= inst_const_C then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				else
					if inst_A then
						compiled[inst_pc] = function()
							if memory[inst_B] == memory[inst_C] then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if memory[inst_B] ~= memory[inst_C] then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				end
			end
		elseif op == 24 then
			-- LT
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB
			local sBx = proto_code[inst_pc + 1].sBx

			if inst_is_KB then
				if inst_is_KC then
					if (inst_const_B < inst_const_C) == inst_A then
						compiled[inst_pc] = function()
							pc = pc + sBx + 1
						end
					else
						compiled[inst_pc] = add_1_to_pc
					end
				else
					if inst_A then
						compiled[inst_pc] = function()
							if inst_const_B < memory[inst_C] then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if not (inst_const_B < memory[inst_C]) then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				end
			else
				if inst_is_KC then
					if inst_A then
						compiled[inst_pc] = function()
							if memory[inst_B] < inst_const_C then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if not (memory[inst_B] < inst_const_C) then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				else
					if inst_A then
						compiled[inst_pc] = function()
							if memory[inst_B] < memory[inst_C] then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if not (memory[inst_B] < memory[inst_C]) then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				end
			end
		elseif op == 25 then
			-- LE
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_const_C = inst.const_C
			local inst_const_B = inst.const_B
			local inst_is_KC = inst.is_KC
			local inst_is_KB = inst.is_KB
			local sBx = proto_code[inst_pc + 1].sBx

			if inst_is_KB then
				if inst_is_KC then
					if (inst_const_B <= inst_const_C) == inst_A then
						compiled[inst_pc] = function()
							pc = pc + sBx + 1
						end
					else
						compiled[inst_pc] = add_1_to_pc
					end
				else
					if inst_A then
						compiled[inst_pc] = function()
							if inst_const_B <= memory[inst_C] then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if not (inst_const_B <= memory[inst_C]) then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				end
			else
				if inst_is_KC then
					if inst_A then
						compiled[inst_pc] = function()
							if memory[inst_B] <= inst_const_C then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if not (memory[inst_B] <= inst_const_C) then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				else
					if inst_A then
						compiled[inst_pc] = function()
							if memory[inst_B] <= memory[inst_C] then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					else
						compiled[inst_pc] = function()
							if not (memory[inst_B] <= memory[inst_C]) then
								pc = pc + sBx
							end
							pc = pc + 1
						end
					end
				end
			end
		elseif op == 27 then
			-- TESTSET
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local sBx = proto_code[inst_pc + 1].sBx

			if inst_C then
				compiled[inst_pc] = function()
					local memory_B = memory[inst_B]
					if memory_B then
						memory[inst_A] = memory_B
						pc = pc + sBx
					end
					pc = pc + 1
				end
			else
				compiled[inst_pc] = function()
					local memory_B = memory[inst_B]
					if not memory_B then
						memory[inst_A] = memory_B
						pc = pc + sBx
					end
					pc = pc + 1
				end
			end
		elseif op == 32 then
			-- FORPREP
			local inst_A = inst.A
			local inst_A_plus_1 = inst_A + 1
			local inst_A_plus_2 = inst_A + 2
			local inst_sBx = inst.sBx
			compiled[inst_pc] = function()
				local init = _tonumber(memory[inst_A])
				if init then
					local limit = _tonumber(memory[inst_A_plus_1])
					if limit then
						local step = _tonumber(memory[inst_A_plus_2])
						if step then
							memory[inst_A] = init - step
							memory[inst_A_plus_1] = limit
							memory[inst_A_plus_2] = step
						else
							_error("`for` step must be a number")
						end
					else
						_error("`for` limit must be a number")
					end
				else
					_error("`for` initial value must be a number")
				end
				pc = pc + inst_sBx
			end
		elseif op == 34 then
			-- SETLIST
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_A_plus_1 = inst_A + 1

			if inst_B == 0 then
				if inst_C == 0 then
					local pos = ((inst[inst_pc + 1].value - 1) * 50) + 1 -- FIELDS_PER_FLUSH = 50
					compiled[inst_pc] = function()
						pc = pc + 1

						table_move(memory, inst_A_plus_1, top_index, pos, memory[inst_A])
					end
				else
					local pos = ((inst_C - 1) * 50) + 1 -- FIELDS_PER_FLUSH = 50

					compiled[inst_pc] = function()
						table_move(memory, inst_A_plus_1, top_index, pos, memory[inst_A])
					end
				end
			else
				if inst_C == 0 then
					local pos = ((inst[inst_pc + 1].value - 1) * 50) + 1 -- FIELDS_PER_FLUSH = 50

					compiled[inst_pc] = function()
						pc = pc + 1

						table_move(memory, inst_A_plus_1, inst_A + inst_B, pos, memory[inst_A])
					end
				else
					local pos = ((inst_C - 1) * 50) + 1 -- FIELDS_PER_FLUSH = 50

					compiled[inst_pc] = function()
						table_move(memory, inst_A_plus_1, inst_A + inst_B, pos, memory[inst_A])
					end
				end
			end
			-- level 5
		elseif op == 11 then
			-- SELF
			local inst_A = inst.A
			local inst_B = inst.B

			local inst_A_plus_1 = inst_A + 1

			if inst.is_KC then
				local inst_const_C = inst.const_C

				compiled[inst_pc] = function()
					local memory_B = memory[inst_B]

					memory[inst_A_plus_1] = memory_B
					memory[inst_A] = memory_B[inst_const_C]
				end
			else
				local inst_C = inst.C

				compiled[inst_pc] = function()
					local memory_B = memory[inst_B]

					memory[inst_A_plus_1] = memory_B
					memory[inst_A] = memory_B[memory[inst_C]]
				end
			end
		elseif op == 28 then
			-- CALL
			local inst_A = inst.A
			local inst_B = inst.B
			local inst_C = inst.C
			local inst_C_minus_1 = inst_C - 1
			local inst_A_plus_1 = inst_A + 1
			local inst_A_minus_1 = inst_A - 1
			if inst_B == 0 then
				if inst_C == 0 then
					local function call(...)
						local ret_count = _select("#", ...)
						top_index = inst_A + ret_count - 1

						for i = 1, ret_count do
							memory[inst_A_minus_1 + i] = _select(i, ...)
						end
					end
					compiled[inst_pc] = function()
						call(memory[inst_A](table_unpack(memory, inst_A_plus_1, top_index)))
					end
				else
					local function call(...)
						for i = 1, inst_C_minus_1 do
							memory[inst_A_minus_1 + i] = _select(i, ...)
						end
					end
					compiled[inst_pc] = function()
						call(memory[inst_A](table_unpack(memory, inst_A_plus_1, top_index)))
					end
				end
			else
				if inst_C == 0 then
					local arg_count = inst_A + inst_B - 1
					local function call(...)
						local ret_count = _select("#", ...)
						top_index = inst_A + ret_count - 1

						for i = 1, ret_count do
							memory[inst_A_minus_1 + i] = _select(i, ...)
						end
					end
					compiled[inst_pc] = function()
						call(memory[inst_A](table_unpack(memory, inst_A_plus_1, arg_count)))
					end
				else
					local arg_count = inst_A + inst_B - 1
					local function call(...)
						for i = 1, inst_C_minus_1 do
							memory[inst_A_minus_1 + i] = _select(i, ...)
						end
					end
					compiled[inst_pc] = function()
						call(memory[inst_A](table_unpack(memory, inst_A_plus_1, arg_count)))
					end
				end
			end
		elseif op == 29 then
			compiled[inst_pc] = false
		elseif op == 30 then
			compiled[inst_pc] = false
		elseif op == 35 then
			-- CLOSE
			local inst_A = inst.A
			compiled[inst_pc] = function()
				for i, uv in open_list do
					local uv_index = uv.index
					if uv_index >= inst_A then
						uv.value = uv.store[uv_index] -- store value
						uv.store = uv
						uv.index = "value" -- self reference
						open_list[i] = nil
					end
				end
			end
		elseif op == 36 then
			-- CLOSURE
			local inst_A = inst.A
			local inst_Bx = inst.Bx
			local sub = proto_subs[inst_Bx + 1] -- offset for 1 based index
			local nups = sub.num_upval

			if nups ~= 0 then
				local pseudos: { { any } } = {}
				for i = 0, nups - 1 do
					local pseudo = proto_code[inst_pc + 1 + i]
					local pseudo_op = pseudo.op
					local pseudo_op_is_move = pseudo_op == 0
					if pseudo_op_is_move or pseudo_op == 4 then
						pseudos[i] = {
							pseudo_op_is_move,
							pseudo.B,
						}
					end
				end

				compiled[inst_pc] = function()
					local uvlist = {}

					for i, pseudo in pseudos do
						local pseudo_op_is_move = pseudo[1]

						if pseudo_op_is_move then -- MOVE
							-- open_lua_upvalue
							local index = pseudo[2]
							local prev = open_list[index]

							if prev then
								uvlist[i] = prev
							else
								local prev = { index = index, store = memory, value = nil }
								open_list[index] = prev
								uvlist[i] = prev
							end
						else -- GETUPVAL
							uvlist[i] = (upvals :: { uv })[pseudo[2]]
						end
					end

					memory[inst_A] = lua_wrap_state(sub, uvlist)

					pc = pc + nups
				end
			else
				compiled[inst_pc] = function()
					memory[inst_A] = lua_wrap_state(sub, nil)
				end
			end
		elseif op == 37 then
			-- VARARG
			local inst_A = inst.A
			local inst_B = inst.B
			if inst_B == 0 then
				local inst_A_minus_1 = inst_A - 1
				compiled[inst_pc] = function()
					top_index = inst_A_minus_1 + vararg_len

					table_move(vararg_list, 1, vararg_len, inst_A, memory)
				end
			else
				compiled[inst_pc] = function()
					table_move(vararg_list, 1, inst_B, inst_A, memory)
				end
			end
		else
			error("Unknown opcode: " .. op)
		end
	end

	local function run()
		while true do
			local inst = compiled[pc]
			if inst then
				pc = pc + 1
				inst()
			else
				local inst_data = proto_code[pc]
				local inst_data_op = inst_data.op
				pc = pc + 1
				if inst_data_op == 30 then
					-- RETURN
					local inst_data_A = inst_data.A
					local inst_data_B = inst_data.B

					local len = if inst_data_B == 0 then top_index - inst_data_A + 1 else inst_data_B - 1

					for i, uv in open_list do
						local uv_index = uv.index
						if uv_index >= 0 then
							uv.value = uv.store[uv_index] -- store value
							uv.store = uv
							uv.index = "value" -- self reference
							open_list[i] = nil
						end
					end

					return table_unpack(memory, inst_data_A, inst_data_A + len - 1)
				elseif inst_data_op == 29 then
					-- TAILCALL
					local inst_data_A = inst_data.A
					local inst_data_B = inst_data.B

					local params = if inst_data_B == 0 then top_index - inst_data_A else inst_data_B - 1

					for i, uv in open_list do
						local uv_index = uv.index
						if uv_index >= 0 then
							uv.value = uv.store[uv_index] -- store value
							uv.store = uv
							uv.index = "value" -- self reference
							open_list[i] = nil
						end
					end

					return memory[inst_data_A](table_unpack(memory, inst_data_A + 1, inst_data_A + params))
				end
				return
			end
		end
	end

	local function handleErrors(success: boolean, ...)
		if success then
			return ...
		else
			_error(
				proto.source .. ":" .. proto.lines[pc - 1] .. ": " .. (... or "Error occurred, no output from Lua."),
				0
			)
		end
	end

	local proto_num_param = proto.num_param
	return function(...)
		local passed = { ... }

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

		top_index = -1
		table_clear(open_list)
		pc = 1

		return handleErrors(_pcall(run))
	end
end

return function(bCode: string)
	return lua_wrap_state(lua_bc_to_state(bCode), nil)
end