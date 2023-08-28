-- Adapted from the amazing Yueliang project
-- http://yueliang.luaforge.net/

--!nolint GlobalUsedAsLocal
--[[----

luac.lua
Primitive luac in Lua
This file is part of Yueliang.

Copyright (c) 2005-2007 Kein-Hong Man <khman@users.sf.net>
The COPYRIGHT file describes the conditions
under which this software may be distributed.

See the ChangeLog for more information.

------]]
--[[----
-- Notes:
-- * based on luac.lua in the test directory of the 5.1.2 distribution
-- * usage: lua luac.lua file.lua
------]]

-- load and initialize the required modules

local table_concat = table.concat

local lua_assert = assert

local math_floor = math.floor
local math_frexp = math.frexp
local math_abs = math.abs
local math_ldexp = math.ldexp

local string_sub = string.sub
local string_char = string.char
local string_byte = string.byte
local string_find = string.find
local string_gmatch = string.gmatch
local string_lower = string.lower
local string_gsub = string.gsub

local string_char_t = {}
for i = 0, 255 do
	string_char_t[i] = string_char(i)
end

local size_size_t = 8

-- Describes how error messages quote program elements.
local function quote(x)
	return "'" .. x .. "'"
end

local LuaState = {} -- dummy, not actually used

-- interfacing to yueliang

-- mark for precompiled code ('<esc>Lua') (from lua.h)
local luaU_LUA_SIGNATURE = "\27Lua"

-- constants for header of binary files (from lundump.h)
local luaU_LUAC_VERSION = 0x51 -- this is Lua 5.1
local luaU_LUAC_FORMAT = 0 -- this is the official format
local luaU_LUAC_HEADERSIZE = 12 -- size of header of binary files

-- FIRST_RESERVED is not required as tokens are manipulated as strings
-- TOKEN_LEN deleted; maximum length of a reserved word not needed

-- "ORDER RESERVED" deleted; enumeration in one place: lexer_RESERVED

-- terminal symbols denoted by reserved words: TK_AND to TK_WHILE
-- other terminal symbols: TK_NAME to TK_EOS
local lexer_RESERVED = [[
TK_AND and
TK_BREAK break
TK_DO do
TK_ELSE else
TK_ELSEIF elseif
TK_END end
TK_FALSE false
TK_FOR for
TK_FUNCTION function
TK_IF if
TK_IN in
TK_LOCAL local
TK_NIL nil
TK_NOT not
TK_OR or
TK_REPEAT repeat
TK_RETURN return
TK_THEN then
TK_TRUE true
TK_UNTIL until
TK_WHILE while
TK_CONCAT ..
TK_DOTS ...
TK_EQ ==
TK_GE >=
TK_LE <=
TK_NE ~=
TK_NAME <name>
TK_NUMBER <number>
TK_STRING <string>
TK_EOS <eof>]]

--[[----
-- Instead of passing seminfo, the Token struct (e.g. lexerState_t) is passed
-- so that lexer functions can use its table element, lexerState_t.seminfo
--
-- SemInfo (struct no longer needed, a mixed-type value is used)
--
-- Token (struct of lexerState_t and lexerState_lookahead):
--   token  -- token symbol
--   seminfo  -- semantics information
--
-- lexerState (struct of lexerState; lexerState is initialized by lexer_setinput):
--   current  -- current character (charint)
--   lineNumber  -- input line counter
--   lastLine  -- line of last token 'consumed'
--   t  -- current token (table: struct Token)
--   lookahead  -- look ahead token (table: struct Token)
--   funcStates  -- 'FuncState' is private to the parser
--   L -- LuaState
--   z  -- input stream
--   buff  -- buffer for tokens
--   source  -- current source name
--   decpoint -- locale decimal point
--   nestlevel  -- level of nested non-terminals
------]]
-- lexer_tokens (was lexer_tokens) is now a hash; see lexer_init

local lexer_MAXSRC = 80
local lexer_MAX_INT = 2147483645 -- constants from elsewhere (see above)
local lexer_LUA_COMPAT_LSTR = 1
--lexer_MAX_SIZET = 4294967293

-- initialize lexer
-- * original lexer_init has code to create and register token strings
-- * lexer_tokens: TK_* -> token
-- * lexer_enums:  token -> TK_* (used in lex)

local luaU_tokens, luaU_enums = {}, {}
for tok, str in string_gmatch(lexer_RESERVED, "(%S+) (%S+)") do
	luaU_tokens[tok] = str
	luaU_enums[str] = tok
end

-- constants used by code generator

-- maximum stack for a Lua function
local luaK_MAXSTACK = 250 -- (from llimits.h)

--[[----
-- other functions
------]]

-- emulation of TValue macros (these are from lobject.h)
-- * TValue is a table since lcode passes references around
-- * tt member field removed, using Lua's type() instead
-- * for setsvalue, sethvalue, parameter L (deleted here) in lobject.h
--   is used in an lua_assert for testing, see checkliveness(g,obj)

local function luaK_ttisnumber(o)
	if o then
		return type(o.value) == "number"
	else
		return false
	end
end

-- The luai_num* macros define the primitive operations over numbers.
-- * this is not the entire set of primitive operations from luaconf.h
-- * used in luaK_constfolding()

local function luaK_numisnan(a)
	-- a NaN cannot equal another NaN

	return a ~= a
end

--[[
===========================================================================
We assume that instructions are unsigned numbers.
All instructions have an opcode in the first 6 bits.
Instructions can have the following fields:
'A' : 8 bits
'B' : 9 bits
'C' : 9 bits
'Bx' : 18 bits ('B' and 'C' together)
'sBx' : signed Bx

A signed argument is represented in excess K; that is, the number
value is the unsigned value minus K. K is exactly the maximum value
for that argument (so that -max is represented by 0, and +max is
represented by 2*max), which is half the maximum for the corresponding
unsigned argument.
===========================================================================
--]]
local luaP_OpMode = { iABC = 0, iABx = 1, iAsBx = 2 } -- basic instruction format

-- size and position of opcode arguments.
-- * WARNING size and position is hard-coded elsewhere in this script

local luaP_SIZE_C = 9
local luaP_SIZE_B = 9
local luaP_SIZE_Bx = luaP_SIZE_C + luaP_SIZE_B
local luaP_SIZE_A = 8

-- limits for opcode arguments.
-- we use (signed) int to manipulate most arguments,
-- so they must fit in LUAI_BITSINT-1 bits (-1 for sign)

-- removed "#if SIZE_Bx < BITS_INT-1" test, assume this script is
-- running on a Lua VM with double or int as LUA_NUMBER

local luaP_MAXARG_Bx = math_ldexp(1, luaP_SIZE_Bx) - 1
local luaP_MAXARG_sBx = math_floor(luaP_MAXARG_Bx / 2) -- 'sBx' is signed

local luaP_MAXARG_A = math_ldexp(1, luaP_SIZE_A) - 1
local luaP_MAXARG_C = math_ldexp(1, luaP_SIZE_C) - 1

-- creates a mask with 'n' 1 bits at position 'p'
-- MASK1(n,p) deleted, not required
-- creates a mask with 'n' 0 bits at position 'p'
-- MASK0(n,p) deleted, not required

--[[----
Visual representation for reference:

 31    |    |     |            0      bit position
+-----+-----+-----+----------+
|  B  |  C  |  A  |  Opcode  |      iABC format
+-----+-----+-----+----------+
-  9  -  9  -  8  -    6     -      field sizes
+-----+-----+-----+----------+
|   [s]Bx   |  A  |  Opcode  |      iABx | iAsBx format
+-----+-----+-----+----------+

------]]

-- the following macros help to manipulate instructions
-- * changed to a table object representation, very clean compared to
--   the [nightmare] alternatives of using a number or a string
-- * Bx is a separate element from B and C, since there is never a need
--   to split Bx in the parser or code generator

-- these accept or return opcodes in the form of string names
local function luaP_GET_OPCODE(i)
	return luaP_ROpCode[i.OP]
end

local function luaP_SET_OPCODE(i, o)
	i.OP = luaP_OpCode[o]
end

local function luaP_GETARG_sBx(i)
	return i.Bx - luaP_MAXARG_sBx
end

local function luaP_SETARG_sBx(i, b)
	i.Bx = b + luaP_MAXARG_sBx
end

local function luaP_CREATE_ABC(o, a, b, c)
	return { OP = luaP_OpCode[o], A = a, B = b, C = c }
end

local function luaP_CREATE_ABx(o, a, bc)
	return { OP = luaP_OpCode[o], A = a, Bx = bc }
end

-- create an instruction from a number (for OP_SETLIST)

local function luaP_CREATE_Inst(c)
	local o = c % 64
	c = (c - o) / 64
	local a = c % 256
	c = (c - a) / 256
	return luaP_CREATE_ABx(o, a, c)
end

-- returns a 4-char string little-endian encoded form of an instruction

local function luaP_Instruction(i)
	if i.Bx then
		-- change to OP/A/B/C format
		i.C = i.Bx % 512
		i.B = (i.Bx - i.C) / 512
	end
	local I = i.A * 64 + i.OP
	local c0 = I % 256
	I = i.C * 64 + (I - c0) / 256 -- 6 bits of A left
	local c1 = I % 256
	I = i.B * 128 + (I - c1) / 256 -- 7 bits of C left
	local c2 = I % 256
	local c3 = (I - c2) / 256
	return string_char(c0, c1, c2, c3)
end

-- Macros to operate RK indices
-- * these use arithmetic instead of bit ops

-- this bit 1 means constant (0 means register)
local luaP_BITRK = math_ldexp(1, luaP_SIZE_B - 1)

-- test whether value is a constant
local function luaP_ISK(x)
	return x >= luaP_BITRK
end

local luaP_MAXINDEXRK = luaP_BITRK - 1

-- code a constant index as a RK value
local function luaP_RKASK(x)
	return x + luaP_BITRK
end

-- invalid register that fits in 8 bits

local luaP_NO_REG = luaP_MAXARG_A

-- R(x) - register
-- Kst(x) - constant (in constant table)

-- grep "ORDER OP" if you change these enums
luaP_OpCode = {} -- lookup name -> number
luaP_ROpCode = {
	[0] = "OP_MOVE", --  A B     R(A) := R(B)
	"OP_LOADK", --       A Bx    R(A) := Kst(Bx)
	"OP_LOADBOOL", --    A B C   R(A) := (Bool)B; if (C) pc++
	"OP_LOADNIL", --     A B     R(A) := ... := R(B) := nil
	"OP_GETUPVAL", --    A B     R(A) := UpValue[B]
	"OP_GETGLOBAL", --   A Bx    R(A) := Gbl[Kst(Bx)]
	"OP_GETTABLE", --    A B C   R(A) := R(B)[RK(C)]
	"OP_SETGLOBAL", --   A Bx    Gbl[Kst(Bx)] := R(A)
	"OP_SETUPVAL", --    A B     UpValue[B] := R(A)
	"OP_SETTABLE", --    A B C   R(A)[RK(B)] := RK(C)
	"OP_NEWTABLE", --    A B C   R(A) := {} (size = B,C)
	"OP_SELF", --        A B C   R(A+1) := R(B); R(A) := R(B)[RK(C)]
	"OP_ADD", --         A B C   R(A) := RK(B) + RK(C)
	"OP_SUB", --         A B C   R(A) := RK(B) - RK(C)
	"OP_MUL", --         A B C   R(A) := RK(B) * RK(C)
	"OP_DIV", --         A B C   R(A) := RK(B) / RK(C)
	"OP_MOD", --         A B C   R(A) := RK(B) % RK(C)
	"OP_POW", --         A B C   R(A) := RK(B) ^ RK(C)
	"OP_UNM", --         A B     R(A) := -R(B)
	"OP_NOT", --         A B     R(A) := not R(B)
	"OP_LEN", --         A B     R(A) := length of R(B)
	"OP_CONCAT", --      A B C   R(A) := R(B).. ... ..R(C)
	"OP_JMP", --         sBx     pc+=sBx
	"OP_EQ", --          A B C   if ((RK(B) == RK(C)) ~= A) then pc++
	"OP_LT", --          A B C   if ((RK(B) <  RK(C)) ~= A) then pc++
	"OP_LE", --          A B C   if ((RK(B) <= RK(C)) ~= A) then pc++
	"OP_TEST", --        A C     if not (R(A) <=> C) then pc++
	"OP_TESTSET", --     A B C   if (R(B) <=> C) then R(A) := R(B) else pc++
	"OP_CALL", --        A B C   R(A), ... ,R(A+C-2) := R(A)(R(A+1), ... ,R(A+B-1))
	"OP_TAILCALL", --    A B C   return R(A)(R(A+1), ... ,R(A+B-1))
	"OP_RETURN", --      A B     return R(A), ... ,R(A+B-2)  (see note)
	"OP_FORLOOP", --     A sBx   R(A)+=R(A+2);
	-- if R(A) <?= R(A+1) then { pc+=sBx; R(A+3)=R(A) }
	"OP_FORPREP", --     A sBx   R(A)-=R(A+2); pc+=sBx
	"OP_TFORLOOP", --    A C     R(A+3), ... ,R(A+2+C) := R(A)(R(A+1), R(A+2));
	-- if R(A+3) ~= nil then R(A+2)=R(A+3) else pc++
	"OP_SETLIST", --     A B C   R(A)[(C-1)*FPF+i] := R(A+i), 1 <= i <= B
	"OP_CLOSE", --       A       close all variables in the stack up to (>=) R(A)
	"OP_CLOSURE", --     A Bx    R(A) := closure(KPROTO[Bx], R(A), ... ,R(A+n))
	"OP_VARARG", --      A B     R(A), R(A+1), ..., R(A+B-1) = vararg
} -- lookup number -> name

-- ORDER OP

for num, v in luaP_ROpCode do
	luaP_OpCode[v] = num
end

--[[
===========================================================================
Notes:
(*) In OP_CALL, if (B == 0) then B = top. C is the number of returns - 1,
and can be 0: OP_CALL then sets 'top' to last_result+1, so
next open instruction (OP_CALL, OP_RETURN, OP_SETLIST) may use 'top'.
(*) In OP_VARARG, if (B == 0) then use actual number of varargs and
set top (like in OP_CALL with C == 0).
(*) In OP_RETURN, if (B == 0) then return up to 'top'
(*) In OP_SETLIST, if (B == 0) then B = 'top';
if (C == 0) then next 'instruction' is real C
(*) For comparisons, A specifies what condition the test should accept
(true or false).
(*) All 'skips' (pc++) assume that next instruction is a jump
===========================================================================
--]]
--[[----
masks for instruction properties. The format is:
bits 0-1: op mode
bits 2-3: C arg mode
bits 4-5: B arg mode
bit 6: instruction set register A
bit 7: operator is a test

for OpArgMask:
OpArgN - argument is not used
OpArgU - argument is used
OpArgR - argument is a register or a jump offuncstateset
OpArgK - argument is a constant or register/constant
------]]
-- was enum OpArgMask
local luaP_OpArgMask = { OpArgN = 0, OpArgU = 1, OpArgR = 2, OpArgK = 3 }

-- e.g. to compare with symbols, luaP_getOpMode(...) == luaP_OpCode.iABC
-- * accepts opcode parameter as strings, e.g. "OP_MOVE"

local function luaP_getOpMode(m)
	return luaP_opmodes[luaP_OpCode[m]] % 4
end

local function luaP_getBMode(m)
	return math_floor(luaP_opmodes[luaP_OpCode[m]] / 16) % 4
end

local function luaP_getCMode(m)
	return math_floor(luaP_opmodes[luaP_OpCode[m]] / 4) % 4
end

local function luaP_testTMode(m)
	return math_floor(luaP_opmodes[luaP_OpCode[m]] / 128)
end

-- number of list items to accumulate before a SETLIST instruction
local luaP_LFIELDS_PER_FLUSH = 50

-- build instruction properties array
-- * deliberately coded to look like the C equivalent

local function opmode(t, a, b, c, m)
	return t * 128 + a * 64 + luaP_OpArgMask[b] * 16 + luaP_OpArgMask[c] * 4 + luaP_OpMode[m]
end

-- ORDER OP
luaP_opmodes = {
	-- T A B C mode opcode
	[0] = opmode(0, 1, "OpArgR", "OpArgN", "iABC"), -- OP_MOVE
	opmode(0, 1, "OpArgK", "OpArgN", "iABx"), -- OP_LOADK
	opmode(0, 1, "OpArgU", "OpArgU", "iABC"), -- OP_LOADBOOL
	opmode(0, 1, "OpArgR", "OpArgN", "iABC"), -- OP_LOADNIL
	opmode(0, 1, "OpArgU", "OpArgN", "iABC"), -- OP_GETUPVAL
	opmode(0, 1, "OpArgK", "OpArgN", "iABx"), -- OP_GETGLOBAL
	opmode(0, 1, "OpArgR", "OpArgK", "iABC"), -- OP_GETTABLE
	opmode(0, 0, "OpArgK", "OpArgN", "iABx"), -- OP_SETGLOBAL
	opmode(0, 0, "OpArgU", "OpArgN", "iABC"), -- OP_SETUPVAL
	opmode(0, 0, "OpArgK", "OpArgK", "iABC"), -- OP_SETTABLE
	opmode(0, 1, "OpArgU", "OpArgU", "iABC"), -- OP_NEWTABLE
	opmode(0, 1, "OpArgR", "OpArgK", "iABC"), -- OP_SELF
	opmode(0, 1, "OpArgK", "OpArgK", "iABC"), -- OP_ADD
	opmode(0, 1, "OpArgK", "OpArgK", "iABC"), -- OP_SUB
	opmode(0, 1, "OpArgK", "OpArgK", "iABC"), -- OP_MUL
	opmode(0, 1, "OpArgK", "OpArgK", "iABC"), -- OP_DIV
	opmode(0, 1, "OpArgK", "OpArgK", "iABC"), -- OP_MOD
	opmode(0, 1, "OpArgK", "OpArgK", "iABC"), -- OP_POW
	opmode(0, 1, "OpArgR", "OpArgN", "iABC"), -- OP_UNM
	opmode(0, 1, "OpArgR", "OpArgN", "iABC"), -- OP_NOT
	opmode(0, 1, "OpArgR", "OpArgN", "iABC"), -- OP_LEN
	opmode(0, 1, "OpArgR", "OpArgR", "iABC"), -- OP_CONCAT
	opmode(0, 0, "OpArgR", "OpArgN", "iAsBx"), -- OP_JMP
	opmode(1, 0, "OpArgK", "OpArgK", "iABC"), -- OP_EQ
	opmode(1, 0, "OpArgK", "OpArgK", "iABC"), -- OP_LT
	opmode(1, 0, "OpArgK", "OpArgK", "iABC"), -- OP_LE
	opmode(1, 1, "OpArgR", "OpArgU", "iABC"), -- OP_TEST
	opmode(1, 1, "OpArgR", "OpArgU", "iABC"), -- OP_TESTSET
	opmode(0, 1, "OpArgU", "OpArgU", "iABC"), -- OP_CALL
	opmode(0, 1, "OpArgU", "OpArgU", "iABC"), -- OP_TAILCALL
	opmode(0, 0, "OpArgU", "OpArgN", "iABC"), -- OP_RETURN
	opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"), -- OP_FORLOOP
	opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"), -- OP_FORPREP
	opmode(1, 0, "OpArgN", "OpArgU", "iABC"), -- OP_TFORLOOP
	opmode(0, 0, "OpArgU", "OpArgU", "iABC"), -- OP_SETLIST
	opmode(0, 0, "OpArgN", "OpArgN", "iABC"), -- OP_CLOSE
	opmode(0, 1, "OpArgU", "OpArgN", "iABx"), -- OP_CLOSURE
	opmode(0, 1, "OpArgU", "OpArgN", "iABC"), -- OP_VARARG
}

--[[----
-- code generator functions
------]]

-- Marks the end of a patch list. It is an invalid value both as an absolute
-- address, and as a list link (would link an element to itself).

local luaK_NO_JUMP = -1

-- grep "ORDER OPR" if you change these enums

local luaK_BinOpr = {
	OPR_ADD = 0,
	OPR_SUB = 1,
	OPR_MUL = 2,
	OPR_DIV = 3,
	OPR_MOD = 4,
	OPR_POW = 5,
	OPR_CONCAT = 6,
	OPR_NE = 7,
	OPR_EQ = 8,
	OPR_LT = 9,
	OPR_LE = 10,
	OPR_GT = 11,
	OPR_GE = 12,
	OPR_AND = 13,
	OPR_OR = 14,
	OPR_NOBINOPR = 15,
}

--[[----
-- Expression descriptor
-- * expkind changed to string constants; parserAssignment was the only
--   function to use a relational operator with this enumeration
-- VVOID       -- no value
-- VNIL        -- no value
-- VTRUE       -- no value
-- VFALSE      -- no value
-- VK          -- info = index of constant in 'k'
-- VKNUM       -- nval = numerical value
-- VLOCAL      -- info = local register
-- VUPVAL,     -- info = index of upvalue in 'upvalues'
-- VGLOBAL     -- info = index of table; aux = index of global name in 'k'
-- VINDEXED    -- info = table register; aux = index register (or 'k')
-- VJMP        -- info = instruction pc
-- VRELOCABLE  -- info = instruction pc
-- VNONRELOC   -- info = result register
-- VCALL       -- info = instruction pc
-- VVARARG     -- info = instruction pc
} ------]]
--[[----
-- * expdesc in Lua 5.1.x has a union u and another struct s; this Lua
--   implementation ignores all instances of u and s usage
-- struct expdesc:
--   k  -- (enum: expkind)
--   info, aux -- (int, int)
--   nval -- (lua_Number)
--   t  -- patch list of 'exit when true'
--   f  -- patch list of 'exit when false'
------]]
--[[----
-- struct upvaldesc:
--   k  -- (lu_byte)
--   info -- (lu_byte)
------]]
--[[----
-- state needed to generate code for a given function
-- struct FuncState:
--   f  -- current function header (table: Proto)
--   h  -- table to find (and reuse) elements in 'k' (table: Table)
--   prev  -- enclosing function (table: FuncState)
--   lexerState  -- lexical state (table: lexerState)
--   L  -- copy of the Lua state (table: lua_State)
--   bl  -- chain of current blocks (table: BlockCnt)
--   pc  -- next position to code (equivalent to 'ncode')
--   lasttarget   -- 'pc' of last 'jump target'
--   jpc  -- list of pending jumps to 'pc'
--   freereg  -- first free register
--   nk  -- number of elements in 'k'
--   np  -- number of elements in 'p'
--   nlocalvars  -- number of elements in 'localvars'
--   nactvar  -- number of active local variables
--   upvalues[LUAI_MAXUPVALUES]  -- upvalues (table: upvaldesc)
--   activeVar[LUAI_MAXVARS]  -- declared-variable stack
------]]

-- constants used by parser
-- * picks up duplicate values from lexer if required

local parserSHRT_MAX = 32767 -- (from <limits.h>)
local parserLUAI_MAXVARS = 200 -- (luaconf.h)
local parserLUAI_MAXUPVALUES = 60 -- (luaconf.h)
parserMAX_INT = lexer_MAX_INT or 2147483645 -- (from llimits.h)
-- * INT_MAX-2 for 32-bit systems
local parserLUAI_MAXCCALLS = 200 -- (from luaconf.h)

local parserVARARG_HASARG = 1 -- (from lobject.h)
-- NOTE: HASARG_MASK is value-specific
local parserHASARG_MASK = 2 -- this was added for a bitop in parlist()
local parserVARARG_ISVARARG = 2
-- NOTE: there is some value-specific code that involves VARARG_NEEDSARG
local parserVARARG_NEEDSARG = 4

parserLUA_MULTRET = -1 -- (lua.h)

-- Translates unary operators tokens if found, otherwise returns
-- OPR_NOUNOPR. getunopr() and getbinopr() are used in subexpr().
-- * used in subexpr()

local function parsergetunopr(op)
	if op == "TK_NOT" then
		return "OPR_NOT"
	elseif op == "-" then
		return "OPR_MINUS"
	elseif op == "#" then
		return "OPR_LEN"
	else
		return "OPR_NOUNOPR"
	end
end

-- Translates binary operator tokens if found, otherwise returns
-- OPR_NOBINOPR. Code generation uses OPR_* style tokens.
-- * used in subexpr()

local parsergetbinopr_table = {
	["+"] = "OPR_ADD",
	["-"] = "OPR_SUB",
	["*"] = "OPR_MUL",
	["/"] = "OPR_DIV",
	["%"] = "OPR_MOD",
	["^"] = "OPR_POW",
	["TK_CONCAT"] = "OPR_CONCAT",
	["TK_NE"] = "OPR_NE",
	["TK_EQ"] = "OPR_EQ",
	["<"] = "OPR_LT",
	["TK_LE"] = "OPR_LE",
	[">"] = "OPR_GT",
	["TK_GE"] = "OPR_GE",
	["TK_AND"] = "OPR_AND",
	["TK_OR"] = "OPR_OR",
}
local function parsergetbinopr(op)
	return parsergetbinopr_table[op] or "OPR_NOBINOPR"
end

-- the following priority table consists of pairs of left/right values
-- for binary operators (was a static const struct); grep for ORDER OPR
-- * the following struct is replaced:
--   static const struct {
--     lu_byte left;  /* left priority for each binary operator */
--     lu_byte right; /* right priority */
--   } priority[] = {  /* ORDER OPR */

local parserpriority = {
	{ 6, 6 },
	{ 6, 6 },
	{ 7, 7 },
	{ 7, 7 },
	{ 7, 7 }, -- `+' `-' `/' `%'
	{ 10, 9 },
	{ 5, 4 }, -- power and concat (right associative)
	{ 3, 3 },
	{ 3, 3 }, -- equality
	{ 3, 3 },
	{ 3, 3 },
	{ 3, 3 },
	{ 3, 3 }, -- order
	{ 2, 2 },
	{ 1, 1 }, -- logical (and/or)
}

local parserUNARY_PRIORITY = 8 -- priority for unary operators

-- Parse subexpressions. Includes handling of unary operators and binary
-- operators. A subexpr is given the rhs priority level of the operator
-- immediately left of it, if any (limit is -1 if none,) and if a binop
-- is found, limit is compared with the lhs priority level of the binop
-- in order to determine which executes first.

-- subexpr -> (simpleexp | unop subexpr) { binop subexpr }
-- where 'binop' is any binary operator with a priority higher than 'limit'
-- * for priority lookups with parserpriority[], 1=left and 2=right
-- * recursively called
-- * used in expr()

-------
-- converts a IEEE754 double number to an 8-byte little-endian string
-- * luaU_from_double() and luaU_from_int() are adapted from ChunkBake
-- * supports +/- Infinity, but not denormals or NaNs
-------
local function luaU_from_double(x)
	local function grab_byte(v)
		local c = v % 256
		return (v - c) / 256, string_char_t[c]
	end
	local sign = 0
	if x < 0 then
		sign = 1
		x = -x
	end
	local mantissa, exponent = math_frexp(x)
	if x == 0 then -- zero
		mantissa, exponent = 0, 0
	elseif x == 1 / 0 then
		mantissa, exponent = 0, 2047
	else
		mantissa = (mantissa * 2 - 1) * math_ldexp(0.5, 53)
		exponent = exponent + 1022
	end

	local x = math_floor(mantissa)

	local x, b1 = grab_byte(x)
	local x, b2 = grab_byte(x)
	local x, b3 = grab_byte(x)
	local x, b4 = grab_byte(x)
	local x, b5 = grab_byte(x)
	local x, b6 = grab_byte(x)

	local x, b7 = grab_byte(exponent * 16 + x)
	local x, b8 = grab_byte(sign * 128 + x)

	return b1 .. b2 .. b3 .. b4 .. b5 .. b6 .. b7 .. b8
end

-------
-- converts a number to a little-endian 32-bit integer string
-- * input value assumed to not overflow, can be signed/unsigned
-------
local function luaU_from_int(x)
	local x = math_floor(x)
	if x < 0 then
		x = 4294967296 + x
	end -- ULONG_MAX+1

	local a = string_char_t[x % 256]
	x = math_floor(x / 256)

	local b = string_char_t[x % 256]
	x = math_floor(x / 256)

	local c = string_char_t[x % 256]
	x = math_floor(x / 256)

	local d = string_char_t[x % 256]
	x = math_floor(x / 256)

	return a .. b .. c .. d
end

-- converts an integer to a "floating point byte", represented as
-- (eeeeexxx), where the real value is (1xxx) * 2^(eeeee - 1) if
-- eeeee != 0 and (xxx) otherwise.

local function parserint2fb(x)
	local e = 0 -- exponent
	while x >= 16 do
		x = math_floor((x + 1) / 2)
		e = e + 1
	end
	if x < 8 then
		return x
	else
		return ((e + 1) * 8) + (x - 8)
	end
end

-- * used only in (lparser) parsersubexpr()

-- table lookups to simplify testing
local luaK_arith_op = {
	OPR_ADD = "OP_ADD",
	OPR_SUB = "OP_SUB",
	OPR_MUL = "OP_MUL",
	OPR_DIV = "OP_DIV",
	OPR_MOD = "OP_MOD",
	OPR_POW = "OP_POW",
}
local luaK_comp_op = {
	OPR_EQ = "OP_EQ",
	OPR_NE = "OP_EQ",
	OPR_LT = "OP_LT",
	OPR_LE = "OP_LE",
	OPR_GT = "OP_LT",
	OPR_GE = "OP_LE",
}
local luaK_comp_cond = {
	OPR_EQ = 1,
	OPR_NE = 0,
	OPR_LT = 1,
	OPR_LE = 1,
	OPR_GT = 0,
	OPR_GE = 0,
}

-- true of the kind of expression produces multiple return values

local function parserhasmultret(k)
	return k == "VCALL" or k == "VVARARG"
end

-- returns a suitably-formatted chunk name or id
-- * from lobject.c, used in llex.c and ldebug.c
-- * the result, out, is returned (was first argument)

local function lexer_chunkid(source, bufflen)
	local first = string_sub(source, 1, 1)
	if first == "=" then
		return string_sub(source, 2, bufflen) -- remove first char
	end
	-- out = "source", or "...source"
	if first == "@" then
		source = string_sub(source, 2) -- skip the '@'
		bufflen = bufflen - #" '...' "
		local l = #source

		local out = ""
		if l > bufflen then
			source = string_sub(source, 1 + l - bufflen) -- get last part of file name
			out = out .. "..."
		end
		out = out .. source
	else -- out = [string "string"]
		local len = string_find(source, "[\n\r]") -- stop at first newline
		len = len and (len - 1) or #source
		bufflen = bufflen - #' [string "..."] '
		if len > bufflen then
			len = bufflen
		end

		local out = '[string "'
		if len < #source then -- must truncate?
			out = out .. string_sub(source, 1, len) .. "..."
		else
			out = out .. source
		end
		out = out .. '"]'
	end
	return
end

-- there is a jump if patch lists are not identical, was a macro
-- * used in luaK_exp2reg(), luaK_exp2anyreg(), luaK_exp2val()

local function luaK_hasjumps(e)
	return e.t ~= e.f
end

local lexerState_decpoint = "."

return function(source, name)
	name = name or "compiled-lua"

	-- func is the function prototype in tabular form; in C, func can
	-- now be used directly by the VM, this can't be done in Lua

	-- parse
	local lexerState_t = {
		token = nil,
	}
	local lexerState_lookahead = {
		seminfo = nil,
		token = "TK_EOS", -- no look-ahead token
	}
	local lexerState_buff = nil
	local lexerState_funcstates = nil

	local lexerState_z_p = 0

	local lexerState_lineNumber = 1
	local lexerState_lastLine = 1
	local lexerState_source = "@" .. name
	local currentCharacter = nil

	local funcstate = {
		upvalues = {},
		activeVar = {},
		f = nil,
		prev = nil,
	}
	-- the following nCcalls initialization added for convenience
	LuaState.nCcalls = 0

	local function lexerCurrIsNewline()
		return currentCharacter == "\n" or currentCharacter == "\r"
	end
	-- gets the next character and returns it
	-- * this is the next() macro in llex.c; see notes at the beginning
	local function lexerNextCharacter()
		lexerState_z_p = lexerState_z_p + 1
		currentCharacter = string_sub(source, lexerState_z_p, lexerState_z_p)
		if currentCharacter == "" then
			currentCharacter = "EOZ"
		end
		return currentCharacter
	end

	--[[----
	-- Support functions for lexer
	-- * all lexer errors eventually reaches lexerror:
	syntaxerror -> lexerror
	------]]

	-- look up token and return keyword if found (also called by parser)

	local function lexer_token2str(token)
		if string_sub(token, 1, 3) ~= "TK_" then
			if string_find(token, "%c") then
				return "char(" .. string_byte(token) .. ")"
			end
			return token
		else
			return luaU_tokens[token]
		end
	end

	-- throws a lexer error
	-- * txtToken has been made local to lexer_lexerror
	-- * can't communicate LUA_ERRSYNTAX, so it is unimplemented

	local function lexer_lexerror(msg, token)
		local buff = lexer_chunkid(lexerState_source, lexer_MAXSRC)
		local msg = buff .. ":" .. lexerState_lineNumber .. ": " .. msg
		if token then
			local function txtToken(token)
				if token == "TK_NAME" or token == "TK_STRING" or token == "TK_NUMBER" then
					return lexerState_buff
				else
					return lexer_token2str(token)
				end
			end
			msg = msg .. " near " .. quote(txtToken(token))
		end
		-- luaD_throw(lexerState->L, LUA_ERRSYNTAX)
		error(msg)
	end

	-- throws a syntax error (mainly called by parser)
	-- * lexerState_t.token has to be set by the function calling lex
	--   (see lexerNext and lexer_lookahead elsewhere in this file)

	local function lexer_syntaxerror(msg)
		lexer_lexerror(msg, lexerState_t.token)
	end

	local function lexer_inclinenumber()
		local old = currentCharacter
		-- lua_assert(currIsNewline())
		lexerNextCharacter() -- skip '\n' or '\r'
		if lexerCurrIsNewline() and currentCharacter ~= old then
			lexerNextCharacter() -- skip '\n\r' or '\r\n'
		end
		lexerState_lineNumber = lexerState_lineNumber + 1
		if lexerState_lineNumber >= lexer_MAX_INT then
			lexer_syntaxerror("chunk has too many lines")
		end
	end

	--[[----
	-- LEXICAL ANALYZER
	------]]

	-- saves the given character into the token buffer
	-- * buffer handling code removed, not used in this implementation
	-- * test for maximum token buffer length not used, makes things faster

	local function lexerSave(c)
		-- if you want to use this, please uncomment lexer_MAX_SIZET further up
		--if #lexerState_buff > luaU_MAX_SIZET then
		--  lexer_lexerror("lexical element too long")
		--end
		lexerState_buff = lexerState_buff .. c
	end

	-- save current character into token buffer, grabs next character
	-- * like lexerNextCharacter, returns the character read for convenience
	local function lexerSaveAndNext()
		lexerSave(currentCharacter)
		return lexerNextCharacter()
	end

	-- checks if current character read is found in the set 'set'
	local function lexer_check_next(set)
		if not string_find(set, currentCharacter, 1, 1) then
			return false
		end
		lexerSaveAndNext()
		return true
	end

	-- retrieve next token, checking the lookahead buffer if necessary
	-- * note that the macro next() in llex.c is now lexerNextCharacter
	-- * utilized used in lparser.c (various places)

	local function lexerNext()
		lexerState_lastLine = lexerState_lineNumber
		if lexerState_lookahead.token ~= "TK_EOS" then -- is there a look-ahead token?
			-- this must be copy-by-value
			lexerState_t.seminfo = lexerState_lookahead.seminfo -- use this one
			lexerState_t.token = lexerState_lookahead.token
			lexerState_lookahead.token = "TK_EOS" -- and discharge it
		else
			lexerState_t.token = lex(lexerState_t) -- read next token
		end
	end

	-- fill in the lookahead buffer
	-- * utilized used in lparser.c:constructor

	local function lexer_lookahead()
		-- lua_assert(lexerState_lookahead.token == "TK_EOS")
		lexerState_lookahead.token = lex(lexerState_lookahead)
	end

	-- LUA_NUMBER
	-- * lexer_read_numeral is the main lexer function to read a number
	-- * lexer_str2d, lexer_buffreplace, lexer_trydecpoint are support functions

	-- string to number converter (was luaO_str2d from lobject.c)
	-- * returns the number, nil if fails (originally returns a boolean)
	-- * conversion function originally lua_str2number(s,p), a macro which
	--   maps to the strtod() function by default (from luaconf.h)

	local function lexer_str2d(s)
		local result = tonumber(s)
		if result then
			return result
		end
		-- conversion failed
		if string_lower(string_sub(s, 1, 2)) == "0x" then -- maybe an hexadecimal constant?
			result = tonumber(s, 16)
			if result then
				return result
			end -- most common case
			-- Was: invalid trailing characters?
			-- In C, this function then skips over trailing spaces.
			-- true is returned if nothing else is found except for spaces.
			-- If there is still something else, then it returns a false.
			-- All this is not necessary using Lua's tonumber.
		end
		return nil
	end

	-- single-character replacement, for locale-aware decimal points

	local function lexer_buffreplace(from, to)
		--local result, buff = "", lexerState_buff
		--for p = 1, #buff do
		--	local c = string_sub(buff, p, p)
		--	if c == from then c = to end
		--	result = result .. c
		--end
		--lexerState_buff = result
		lexerState_buff = string_gsub(
			lexerState_buff,
			string_gsub(from, "[%(%)%.%%%+%-%*%?%[%]%^%$]", "%%%0"), -- escape magic characters
			to
		)
	end

	-- Attempt to convert a number by translating '.' decimal points to
	-- the decimal point character used by the current locale. This is not
	-- needed in Yueliang as Lua's tonumber() is already locale-aware.
	-- Instead, the code is here in case the user implements localeconv().

	local function lexer_trydecpoint(Token)
		-- format error: try to update decimal point separator
		local old = lexerState_decpoint
		-- translate the following to Lua if you implement localeconv():
		-- struct lconv *cv = localeconv();
		-- lexerState->decpoint = (cv ? cv->decimal_point[0] : '.');
		lexer_buffreplace(old, lexerState_decpoint) -- try updated decimal separator
		local seminfo = lexer_str2d(lexerState_buff)
		Token.seminfo = seminfo
		if not seminfo then
			-- format error with correct decimal point: no more options
			lexer_buffreplace(lexerState_decpoint, ".") -- undo change (for error message)
			lexer_lexerror("malformed number", "TK_NUMBER")
		end
	end

	-- main number conversion function
	-- * "^%w$" needed in the scan in order to detect "EOZ"

	local function lexer_read_numeral(Token)
		-- lua_assert(string_find(currentCharacter, "%d"))
		repeat
			lexerSaveAndNext()
		until string_find(currentCharacter, "%D") and currentCharacter ~= "."
		if lexer_check_next("Ee") then -- 'E'?
			lexer_check_next("+-") -- optional exponent sign
		end
		while string_find(currentCharacter, "^%w$") or currentCharacter == "_" do
			lexerSaveAndNext()
		end
		lexer_buffreplace(".", lexerState_decpoint) -- follow locale for decimal point
		local seminfo = lexer_str2d(lexerState_buff)
		Token.seminfo = seminfo
		if not seminfo then -- format error?
			lexer_trydecpoint(Token) -- try to update decimal point separator
		end
	end

	-- count separators ("=") in a long string delimiter
	-- * used by lexer_read_long_string

	local function lexer_skip_sep()
		local count = 0
		local s = currentCharacter
		-- lua_assert(s == "[" or s == "]")
		lexerSaveAndNext()
		while currentCharacter == "=" do
			lexerSaveAndNext()
			count = count + 1
		end
		return (currentCharacter == s) and count or -count - 1
	end

	-- reads a long string or long comment

	local function lexer_read_long_string(Token, sep)
		local cont = 0
		lexerSaveAndNext() -- skip 2nd '['
		if lexerCurrIsNewline() then -- string starts with a newline?
			lexer_inclinenumber() -- skip it
		end
		while true do
			local c = currentCharacter
			if c == "EOZ" then
				lexer_lexerror(Token and "unfinished long string" or "unfinished long comment", "TK_EOS")
			elseif c == "[" then
				--# compatibility code start
				if lexer_LUA_COMPAT_LSTR then
					if lexer_skip_sep() == sep then
						lexerSaveAndNext() -- skip 2nd '['
						cont = cont + 1
						--# compatibility code start
						if lexer_LUA_COMPAT_LSTR == 1 then
							if sep == 0 then
								lexer_lexerror("nesting of [[...]] is deprecated", "[")
							end
						end
						--# compatibility code end
					end
				end
				--# compatibility code end
			elseif c == "]" then
				if lexer_skip_sep() == sep then
					lexerSaveAndNext() -- skip 2nd ']'
					--# compatibility code start
					if lexer_LUA_COMPAT_LSTR and lexer_LUA_COMPAT_LSTR == 2 then
						cont = cont - 1
						if sep == 0 and cont >= 0 then
							break
						end
					end
					--# compatibility code end
					break
				end
			elseif lexerCurrIsNewline() then
				lexerSave("\n")
				lexer_inclinenumber()
				if not Token then
					lexerState_buff = ""
				end -- avoid wasting space
			else -- default
				if Token then
					lexerSaveAndNext()
				else
					lexerNextCharacter()
				end
			end --if c
		end --while
		if Token then
			local p = 3 + sep
			Token.seminfo = string_sub(lexerState_buff, p, -p)
		end
	end

	-- reads a string
	-- * has been restructured significantly compared to the original C code

	local function lexerReadString(del, Token)
		lexerSaveAndNext()
		while currentCharacter ~= del do
			local c = currentCharacter
			if c == "EOZ" then
				lexer_lexerror("unfinished string", "TK_EOS")
			elseif lexerCurrIsNewline() then
				lexer_lexerror("unfinished string", "TK_STRING")
			elseif c == "\\" then
				local c = lexerNextCharacter() -- do not save the '\'
				if lexerCurrIsNewline() then -- go through
					lexerSave("\n")
					lexer_inclinenumber()
				elseif c ~= "EOZ" then -- will raise an error next loop
					-- escapes handling greatly simplified here:
					local i = string_find("abfnrtv", c, 1, true)
					if i then
						lexerSave(string_sub("\a\b\f\n\r\t\v", i, i))
						lexerNextCharacter()
					elseif not string_find(c, "%d") then
						lexerSaveAndNext() -- handles \\, \", \', and \?
					else -- \xxx
						local c, i = 0, 0
						repeat
							c = 10 * c + currentCharacter
							lexerNextCharacter()
							i = i + 1
						until i >= 3 or not string_find(currentCharacter, "%d")
						if c > 255 then -- UCHAR_MAX
							lexer_lexerror("escape sequence too large", "TK_STRING")
						end
						lexerSave(string_char_t[c])
					end
				end
			else
				lexerSaveAndNext()
			end --if c
		end --while
		lexerSaveAndNext() -- skip delimiter
		Token.seminfo = string_sub(lexerState_buff, 2, -2)
	end

	-- main lexer function

	function lex(Token)
		lexerState_buff = ""
		while true do
			local c = currentCharacter
			if lexerCurrIsNewline() then
				lexer_inclinenumber()
			elseif c == "-" then
				local c = lexerNextCharacter()
				if c ~= "-" then
					return "-"
				end
				-- else is a comment
				local sep = -1
				if lexerNextCharacter() == "[" then
					sep = lexer_skip_sep()
					lexerState_buff = "" -- 'skip_sep' may dirty the buffer
				end
				if sep >= 0 then
					lexer_read_long_string(nil, sep) -- long comment
					lexerState_buff = ""
				else -- else short comment
					while not lexerCurrIsNewline() and currentCharacter ~= "EOZ" do
						lexerNextCharacter()
					end
				end
			elseif c == "[" then
				local sep = lexer_skip_sep()
				if sep >= 0 then
					lexer_read_long_string(Token, sep)
					return "TK_STRING"
				elseif sep == -1 then
					return "["
				else
					lexer_lexerror("invalid long string delimiter", "TK_STRING")
				end
			elseif c == "=" then
				local c = lexerNextCharacter()
				if c ~= "=" then
					return "="
				else
					lexerNextCharacter()
					return "TK_EQ"
				end
			elseif c == "<" then
				local c = lexerNextCharacter()
				if c ~= "=" then
					return "<"
				else
					lexerNextCharacter()
					return "TK_LE"
				end
			elseif c == ">" then
				local c = lexerNextCharacter()
				if c ~= "=" then
					return ">"
				else
					lexerNextCharacter()
					return "TK_GE"
				end
			elseif c == "~" then
				local c = lexerNextCharacter()
				if c ~= "=" then
					return "~"
				else
					lexerNextCharacter()
					return "TK_NE"
				end
			elseif c == '"' or c == "'" then
				lexerReadString(c, Token)
				return "TK_STRING"
			elseif c == "." then
				local c = lexerSaveAndNext()
				if lexer_check_next(".") then
					if lexer_check_next(".") then
						return "TK_DOTS" -- ...
					else
						return "TK_CONCAT" -- ..
					end
				elseif not string_find(c, "%d") then
					return "."
				else
					lexer_read_numeral(Token)
					return "TK_NUMBER"
				end
			elseif c == "EOZ" then
				return "TK_EOS"
			else -- default
				if string_find(c, "%s") then
					-- lua_assert(lexerCurrIsNewline())
					lexerNextCharacter()
				elseif string_find(c, "%d") then
					lexer_read_numeral(Token)
					return "TK_NUMBER"
				elseif string_find(c, "[_%a]") then
					-- identifier or reserved word
					while true do
						local c = lexerSaveAndNext()
						if c == "EOZ" or not string_find(c, "[_%w]") then
							break
						end
					end
					local ts = lexerState_buff
					local tok = luaU_enums[ts]
					if tok then
						return tok
					end -- reserved word?
					Token.seminfo = ts
					return "TK_NAME"
				else
					lexerNextCharacter()
					return c -- single-char tokens (+ - / ...)
				end
			end --if c
		end --while
	end

	-- returns the instruction object for given e (expdesc), was a macro

	local function luaK_getcode(funcStates, e)
		return funcStates.f.code[e.info]
	end

	-- codes an instruction with a signed Bx (sBx) field, was a macro
	-- * used in luaK_jump(), (lparser) parserforbody()

	local function luaK_codeAsBx(funcStates, o, A, sBx)
		return luaK_codeABx(funcStates, o, A, sBx + luaP_MAXARG_sBx)
	end

	-- set the expdesc e instruction for multiple returns, was a macro

	local function luaK_setmultret(funcStates, e)
		luaK_setreturns(funcStates, e, parserLUA_MULTRET)
	end

	-- true if the expression is a constant number (for constant folding)
	-- * used in constfolding(), infix()

	local function luaK_isnumeral(e)
		return e.k == "VKNUM" and e.t == luaK_NO_JUMP and e.f == luaK_NO_JUMP
	end

	-- codes loading of nil, optimization done if consecutive locations
	-- * used in luaK_discharge2reg(), (lparser) parseradjust_assign()

	local function luaK__nil(funcStates, from, n)
		if funcStates.pc > funcStates.lasttarget then -- no jumps to current position?
			if funcStates.pc == 0 then -- function start?
				if from >= funcStates.nactvar then
					return -- positions are already clean
				end
			else
				local previous = funcStates.f.code[funcStates.pc - 1]
				if luaP_GET_OPCODE(previous) == "OP_LOADNIL" then
					local pfrom = previous.A
					local pto = previous.B
					if pfrom <= from and from <= pto + 1 then -- can connect both?
						if from + n - 1 > pto then
							previous.B = from + n - 1
						end
						return
					end
				end
			end
		end
		luaK_codeABC(funcStates, "OP_LOADNIL", from, from + n - 1, 0) -- else no optimization
	end

	-- * used in multiple locations

	local function luaK_jump(funcStates)
		local jpc = funcStates.jpc -- save list of jumps to here
		funcStates.jpc = luaK_NO_JUMP
		local j = luaK_codeAsBx(funcStates, "OP_JMP", 0, luaK_NO_JUMP)
		j = luaK_concat(funcStates, j, jpc) -- keep them on hold
		return j
	end

	-- codes a RETURN instruction
	-- * used in parserclose_func(), parserretstat()

	local function luaK_ret(funcStates, first, nret)
		luaK_codeABC(funcStates, "OP_RETURN", first, nret + 1, 0)
	end

	-- * used in luaK_jumponcond(), luaK_codecomp()

	local function luaK_condjump(funcStates, op, A, B, C)
		luaK_codeABC(funcStates, op, A, B, C)
		return luaK_jump(funcStates)
	end

	-- * used in luaK_patchlistaux(), luaK_concat()

	local function luaK_fixjump(funcStates, pc, dest)
		local jmp = funcStates.f.code[pc]
		local offuncstateset = dest - (pc + 1)
		lua_assert(dest ~= luaK_NO_JUMP)
		if math_abs(offuncstateset) > luaP_MAXARG_sBx then
			lexer_syntaxerror("control structure too long")
		end
		luaP_SETARG_sBx(jmp, offuncstateset)
	end

	-- returns current 'pc' and marks it as a jump target (to avoid wrong
	-- optimizations with consecutive instructions not in the same basic block).
	-- * used in multiple locations
	-- * funcStates.lasttarget tested only by luaK__nil() when optimizing OP_LOADNIL

	local function luaK_getLabel(funcStates)
		local pc = funcStates.pc
		funcStates.lasttarget = pc
		return pc
	end

	-- * used in luaK_need_value(), luaK_removevalues(), luaK_patchlistaux(),
	--   luaK_concat()

	local function luaK_getjump(funcStates, pc)
		local offuncstateset = luaP_GETARG_sBx(funcStates.f.code[pc])
		if offuncstateset == luaK_NO_JUMP then -- point to itself represents end of list
			return luaK_NO_JUMP -- end of list
		else
			return (pc + 1) + offuncstateset -- turn offuncstateset into absolute position
		end
	end

	-- * used in luaK_need_value(), luaK_patchtestreg(), luaK_invertjump()

	local function luaK_getjumpcontrol(funcStates, pc)
		local pi = funcStates.f.code[pc]
		local ppi = funcStates.f.code[pc - 1]
		if pc >= 1 and luaP_testTMode(luaP_GET_OPCODE(ppi)) ~= 0 then
			return ppi
		else
			return pi
		end
	end

	-- check whether list has any jump that do not produce a value
	-- (or produce an inverted value)
	-- * return value changed to boolean
	-- * used only in luaK_exp2reg()

	local function luaK_need_value(funcStates, list)
		while list ~= luaK_NO_JUMP do
			local i = luaK_getjumpcontrol(funcStates, list)
			if luaP_GET_OPCODE(i) ~= "OP_TESTSET" then
				return true
			end
			list = luaK_getjump(funcStates, list)
		end
		return false -- not found
	end

	-- * used in luaK_removevalues(), luaK_patchlistaux()

	local function luaK_patchtestreg(funcStates, node, reg)
		local i = luaK_getjumpcontrol(funcStates, node)
		if luaP_GET_OPCODE(i) ~= "OP_TESTSET" then
			return false -- cannot patch other instructions
		end
		if reg ~= luaP_NO_REG and reg ~= i.B then
			i.A = reg
		else -- no register to put value or register already has the value
			-- due to use of a table as i, i cannot be replaced by another table
			-- so the following is required; there is no change to ARG_C
			luaP_SET_OPCODE(i, "OP_TEST")
			local b = i.B
			i.A = b
			i.B = 0
			-- *i = CREATE_ABC(OP_TEST, GETARG_B(*i), 0, GETARG_C(*i)); /* C */
		end
		return true
	end

	-- * used only in luaK_codenot()

	local function luaK_removevalues(funcStates, list)
		while list ~= luaK_NO_JUMP do
			luaK_patchtestreg(funcStates, list, luaP_NO_REG)
			list = luaK_getjump(funcStates, list)
		end
	end

	-- * used in luaK_dischargejpc(), luaK_patchlist(), luaK_exp2reg()

	local function luaK_patchlistaux(funcStates, list, vtarget, reg, dtarget)
		while list ~= luaK_NO_JUMP do
			local _next = luaK_getjump(funcStates, list)
			if luaK_patchtestreg(funcStates, list, reg) then
				luaK_fixjump(funcStates, list, vtarget)
			else
				luaK_fixjump(funcStates, list, dtarget) -- jump to default target
			end
			list = _next
		end
	end

	-- * used only in luaK_code()

	local function luaK_dischargejpc(funcStates)
		luaK_patchlistaux(funcStates, funcStates.jpc, funcStates.pc, luaP_NO_REG, funcStates.pc)
		funcStates.jpc = luaK_NO_JUMP
	end

	-- * used in (lparser) parserwhilestat(), parserRepeatStatement(), parserforbody()

	local function luaK_patchlist(funcStates, list, target)
		if target == funcStates.pc then
			luaK_patchtohere(funcStates, list)
		else
			lua_assert(target < funcStates.pc)
			luaK_patchlistaux(funcStates, list, target, luaP_NO_REG, target)
		end
	end

	-- * used in multiple locations

	function luaK_patchtohere(funcStates, list)
		luaK_getLabel(funcStates)
		funcStates.jpc = luaK_concat(funcStates, funcStates.jpc, list)
	end

	-- * l1 was a pointer, now l1 is returned and callee assigns the value
	-- * used in multiple locations

	function luaK_concat(funcStates, l1, l2)
		if l2 == luaK_NO_JUMP then
			return l1
		elseif l1 == luaK_NO_JUMP then
			return l2
		else
			local list = l1
			local _next = luaK_getjump(funcStates, list)
			while _next ~= luaK_NO_JUMP do -- find last element
				list = _next
				_next = luaK_getjump(funcStates, list)
			end
			luaK_fixjump(funcStates, list, l2)
		end
		return l1
	end

	-- * used in luaK_reserveRegisters(), (lparser) parserforlist()

	local function luaK_checkstack(funcStates, n)
		local newstack = funcStates.freereg + n
		if newstack > funcStates.f.maxStackSize then
			if newstack >= luaK_MAXSTACK then
				lexer_syntaxerror("function or expression too complex")
			end
			funcStates.f.maxStackSize = newstack
		end
	end

	-- * used in multiple locations

	local function luaK_reserveRegisters(funcStates, n)
		luaK_checkstack(funcStates, n)
		funcStates.freereg = funcStates.freereg + n
	end

	-- * used in luaK_freeexp(), luaK_dischargeVars()

	local function luaK_freereg(funcStates, reg)
		if not luaP_ISK(reg) and reg >= funcStates.nactvar then
			funcStates.freereg = funcStates.freereg - 1
			lua_assert(reg == funcStates.freereg)
		end
	end

	-- * used in multiple locations

	local function luaK_freeexp(funcStates, e)
		if e.k == "VNONRELOC" then
			luaK_freereg(funcStates, e.info)
		end
	end

	-- * TODO NOTE implementation is not 100% correct, since the lua_assert fails
	-- * luaH_set, setobj deleted; direct table access used instead
	-- * used in luaK_stringK(), luaK_numberK(), luaK_boolK(), luaK_nilK()

	local function luaK_addk(funcStates, k, v)
		local idx = funcStates.h[k.value]
		--TValue *idx = luaH_set(L, funcStates->h, k); /* C */
		local f = funcStates.f
		if luaK_ttisnumber(idx) then
			--TODO this lua_assert currently FAILS (last tested for 5.0.2)
			--lua_assert(funcStates.f.k[idx.value] == v)
			--lua_assert(luaO_rawequalObj(&funcStates->f->k[cast_int(nvalue(idx))], v)); /* C */
			return idx.value
		else -- constant not found; create a new entry
			idx = { value = funcStates.nk }
			funcStates.h[k.value] = idx
			-- setnvalue(idx, cast_num(funcStates->nk)); /* C */
			parsergrowvector(funcStates.nk, luaP_MAXARG_Bx, "constant table overflow")
			-- loop to initialize empty f.k positions not required
			f.k[funcStates.nk] = v
			-- setobj(L, &f->k[funcStates->nk], v); /* C */
			-- luaC_barrier(L, f, v); /* GC */
			local nk = funcStates.nk
			funcStates.nk = nk + 1
			return nk
		end
	end

	-- creates and sets a nil object
	-- * used only in luaK_exp2RK()

	local function luaK_nilK(funcStates)
		local k, v = { value = funcStates.h }, {} -- TValue
		-- cannot use nil as key; instead use table itself to represent nil
		return luaK_addk(funcStates, k, v)
	end

	-- * used in luaK_setmultret(), (lparser) parseradjust_assign()

	function luaK_setreturns(funcStates, e, nresults)
		if e.k == "VCALL" then -- expression is an open function call?
			luaK_getcode(funcStates, e).C = nresults + 1
		elseif e.k == "VVARARG" then
			luaK_getcode(funcStates, e).B = nresults + 1
			luaK_getcode(funcStates, e).A = funcStates.freereg
			luaK_reserveRegisters(funcStates, 1)
		end
	end

	-- * used in luaK_dischargeVars(), (lparser) parserAssignment()

	local function luaK_setoneret(funcStates, e)
		if e.k == "VCALL" then -- expression is an open function call?
			e.k = "VNONRELOC"
			e.info = luaK_getcode(funcStates, e).A
		elseif e.k == "VVARARG" then
			luaK_getcode(funcStates, e).B = 2
			e.k = "VRELOCABLE" -- can relocate its simple result
		end
	end

	-- * used in multiple locations

	local function luaK_dischargeVars(funcStates, e)
		local k = e.k
		if k == "VLOCAL" then
			e.k = "VNONRELOC"
		elseif k == "VUPVAL" then
			e.info = luaK_codeABC(funcStates, "OP_GETUPVAL", 0, e.info, 0)
			e.k = "VRELOCABLE"
		elseif k == "VGLOBAL" then
			e.info = luaK_codeABx(funcStates, "OP_GETGLOBAL", 0, e.info)
			e.k = "VRELOCABLE"
		elseif k == "VINDEXED" then
			luaK_freereg(funcStates, e.aux)
			luaK_freereg(funcStates, e.info)
			e.info = luaK_codeABC(funcStates, "OP_GETTABLE", 0, e.info, e.aux)
			e.k = "VRELOCABLE"
		elseif k == "VVARARG" or k == "VCALL" then
			luaK_setoneret(funcStates, e)
		else
			-- there is one value available (somewhere)
		end
	end

	-- * used only in luaK_exp2reg()

	local function luaK_code_label(funcStates, A, b, jump)
		luaK_getLabel(funcStates) -- those instructions may be jump targets
		return luaK_codeABC(funcStates, "OP_LOADBOOL", A, b, jump)
	end

	do
		local function f(funcStates, s)
			local o = { value = s } -- TValue
			return luaK_addk(funcStates, o, o)
		end

		-- creates and sets a string object
		-- * used in (lparser) parsercodestring(), parsersinglevar()
		luaK_stringK = f

		-- creates and sets a number object
		-- * used in luaK_prefix() for negative (or negation of) numbers
		-- * used in (lparser) parsersimpleexp(), parserfornum()

		luaK_numberK = f

		-- creates and sets a boolean object
		-- * used only in luaK_exp2RK()

		luaK_boolK = f
	end

	-- * used in luaK_discharge2AnyReg(), luaK_exp2reg()

	local function luaK_discharge2reg(funcStates, e, reg)
		luaK_dischargeVars(funcStates, e)
		local k = e.k
		if k == "VNIL" then
			luaK__nil(funcStates, reg, 1)
		elseif k == "VFALSE" or k == "VTRUE" then
			luaK_codeABC(funcStates, "OP_LOADBOOL", reg, (k == "VTRUE") and 1 or 0, 0)
		elseif k == "VK" then
			luaK_codeABx(funcStates, "OP_LOADK", reg, e.info)
		elseif k == "VKNUM" then
			luaK_codeABx(funcStates, "OP_LOADK", reg, luaK_numberK(funcStates, e.nval))
		elseif k == "VRELOCABLE" then
			local pc = luaK_getcode(funcStates, e)
			pc.A = reg
		elseif k == "VNONRELOC" then
			if reg ~= e.info then
				luaK_codeABC(funcStates, "OP_MOVE", reg, e.info, 0)
			end
		else
			lua_assert(k == "VVOID" or k == "VJMP")
			return -- nothing to do...
		end
		e.info = reg
		e.k = "VNONRELOC"
	end

	-- * used in luaK_jumponcond(), luaK_codenot()

	local function luaK_discharge2AnyReg(funcStates, e)
		if e.k ~= "VNONRELOC" then
			luaK_reserveRegisters(funcStates, 1)
			luaK_discharge2reg(funcStates, e, funcStates.freereg - 1)
		end
	end

	-- * used in luaK_exp2nextreg(), luaK_exp2anyreg(), luaK_storeVar()

	function luaK_exp2reg(funcStates, e, reg)
		luaK_discharge2reg(funcStates, e, reg)
		if e.k == "VJMP" then
			e.t = luaK_concat(funcStates, e.t, e.info) -- put this jump in 't' list
		end
		if luaK_hasjumps(e) then
			local final -- position after whole expression
			local p_f = luaK_NO_JUMP -- position of an eventual LOAD false
			local p_t = luaK_NO_JUMP -- position of an eventual LOAD true
			if luaK_need_value(funcStates, e.t) or luaK_need_value(funcStates, e.f) then
				local fj = (e.k == "VJMP") and luaK_NO_JUMP or luaK_jump(funcStates)
				p_f = luaK_code_label(funcStates, reg, 0, 1)
				p_t = luaK_code_label(funcStates, reg, 1, 0)
				luaK_patchtohere(funcStates, fj)
			end
			final = luaK_getLabel(funcStates)
			luaK_patchlistaux(funcStates, e.f, final, reg, p_f)
			luaK_patchlistaux(funcStates, e.t, final, reg, p_t)
		end
		e.f, e.t = luaK_NO_JUMP, luaK_NO_JUMP
		e.info = reg
		e.k = "VNONRELOC"
	end

	-- * used in multiple locations

	local function luaK_exp2nextreg(funcStates, e)
		luaK_dischargeVars(funcStates, e)
		luaK_freeexp(funcStates, e)
		luaK_reserveRegisters(funcStates, 1)
		luaK_exp2reg(funcStates, e, funcStates.freereg - 1)
	end

	-- * used in multiple locations

	local function luaK_exp2anyreg(funcStates, e)
		luaK_dischargeVars(funcStates, e)
		if e.k == "VNONRELOC" then
			if not luaK_hasjumps(e) then -- exp is already in a register
				return e.info
			end
			if e.info >= funcStates.nactvar then -- reg. is not a local?
				luaK_exp2reg(funcStates, e, e.info) -- put value on it
				return e.info
			end
		end
		luaK_exp2nextreg(funcStates, e) -- default
		return e.info
	end

	-- * used in luaK_exp2RK(), luaK_prefix(), luaK_posfix()
	-- * used in (lparser) parseryindex()

	local function luaK_exp2val(funcStates, e)
		if luaK_hasjumps(e) then
			luaK_exp2anyreg(funcStates, e)
		else
			luaK_dischargeVars(funcStates, e)
		end
	end

	-- * used in multiple locations

	local function luaK_exp2RK(funcStates, e)
		luaK_exp2val(funcStates, e)
		local k = e.k
		if k == "VKNUM" or k == "VTRUE" or k == "VFALSE" or k == "VNIL" then
			if funcStates.nk <= luaP_MAXINDEXRK then -- constant fit in RK operand?
				-- converted from a 2-deep ternary operator expression
				if e.k == "VNIL" then
					e.info = luaK_nilK(funcStates)
				else
					e.info = (e.k == "VKNUM") and luaK_numberK(funcStates, e.nval)
						or luaK_boolK(funcStates, e.k == "VTRUE")
				end
				e.k = "VK"
				return luaP_RKASK(e.info)
			end
		elseif k == "VK" then
			if e.info <= luaP_MAXINDEXRK then -- constant fit in argC?
				return luaP_RKASK(e.info)
			end
		else
			-- default
		end
		-- not a constant in the right range: put it in a register
		return luaK_exp2anyreg(funcStates, e)
	end

	-- * used in (lparser) parserAssignment(), parserlocalfunc(), parserfuncstat()

	local function luaK_storeVar(funcStates, var, ex)
		local k = var.k
		if k == "VLOCAL" then
			luaK_freeexp(funcStates, ex)
			luaK_exp2reg(funcStates, ex, var.info)
			return
		elseif k == "VUPVAL" then
			local e = luaK_exp2anyreg(funcStates, ex)
			luaK_codeABC(funcStates, "OP_SETUPVAL", e, var.info, 0)
		elseif k == "VGLOBAL" then
			local e = luaK_exp2anyreg(funcStates, ex)
			luaK_codeABx(funcStates, "OP_SETGLOBAL", e, var.info)
		elseif k == "VINDEXED" then
			local e = luaK_exp2RK(funcStates, ex)
			luaK_codeABC(funcStates, "OP_SETTABLE", var.info, var.aux, e)
		else
			lua_assert(0) -- invalid var kind to store
		end
		luaK_freeexp(funcStates, ex)
	end

	-- * used only in (lparser) parserprimaryexp()

	local function luaK__self(funcStates, e, key)
		luaK_exp2anyreg(funcStates, e)
		luaK_freeexp(funcStates, e)
		local func = funcStates.freereg
		luaK_reserveRegisters(funcStates, 2)
		luaK_codeABC(funcStates, "OP_SELF", func, e.info, luaK_exp2RK(funcStates, key))
		luaK_freeexp(funcStates, key)
		e.info = func
		e.k = "VNONRELOC"
	end

	-- * used in luaK_goiftrue(), luaK_codenot()

	local function luaK_invertjump(funcStates, e)
		local pc = luaK_getjumpcontrol(funcStates, e.info)
		lua_assert(
			luaP_testTMode(luaP_GET_OPCODE(pc)) ~= 0
				and luaP_GET_OPCODE(pc) ~= "OP_TESTSET"
				and luaP_GET_OPCODE(pc) ~= "OP_TEST"
		)
		pc.A = (pc.A == 0) and 1 or 0
	end

	-- * used in luaK_goiftrue(), luaK_goiffalse()

	local function luaK_jumponcond(funcStates, e, cond)
		if e.k == "VRELOCABLE" then
			local ie = luaK_getcode(funcStates, e)
			if luaP_GET_OPCODE(ie) == "OP_NOT" then
				funcStates.pc = funcStates.pc - 1 -- remove previous OP_NOT
				return luaK_condjump(funcStates, "OP_TEST", ie.B, 0, cond and 0 or 1)
			end
			-- else go through
		end
		luaK_discharge2AnyReg(funcStates, e)
		luaK_freeexp(funcStates, e)
		return luaK_condjump(funcStates, "OP_TESTSET", luaP_NO_REG, e.info, cond and 1 or 0)
	end

	-- * used in luaK_infix(), (lparser) parsercond()

	local function luaK_goiftrue(funcStates, e)
		local pc -- pc of last jump
		luaK_dischargeVars(funcStates, e)
		local k = e.k
		if k == "VK" or k == "VKNUM" or k == "VTRUE" then
			pc = luaK_NO_JUMP -- always true; do nothing
		elseif k == "VFALSE" then
			pc = luaK_jump(funcStates) -- always jump
		elseif k == "VJMP" then
			luaK_invertjump(funcStates, e)
			pc = e.info
		else
			pc = luaK_jumponcond(funcStates, e, false)
		end
		e.f = luaK_concat(funcStates, e.f, pc) -- insert last jump in `f' list
		luaK_patchtohere(funcStates, e.t)
		e.t = luaK_NO_JUMP
	end

	-- * used in luaK_infix()

	local function luaK_goiffalse(funcStates, e)
		local pc -- pc of last jump
		luaK_dischargeVars(funcStates, e)
		local k = e.k
		if k == "VNIL" or k == "VFALSE" then
			pc = luaK_NO_JUMP -- always false; do nothing
		elseif k == "VTRUE" then
			pc = luaK_jump(funcStates) -- always jump
		elseif k == "VJMP" then
			pc = e.info
		else
			pc = luaK_jumponcond(funcStates, e, true)
		end
		e.t = luaK_concat(funcStates, e.t, pc) -- insert last jump in `t' list
		luaK_patchtohere(funcStates, e.f)
		e.f = luaK_NO_JUMP
	end

	-- * used only in luaK_prefix()

	local function luaK_codenot(funcStates, e)
		luaK_dischargeVars(funcStates, e)
		local k = e.k
		if k == "VNIL" or k == "VFALSE" then
			e.k = "VTRUE"
		elseif k == "VK" or k == "VKNUM" or k == "VTRUE" then
			e.k = "VFALSE"
		elseif k == "VJMP" then
			luaK_invertjump(funcStates, e)
		elseif k == "VRELOCABLE" or k == "VNONRELOC" then
			luaK_discharge2AnyReg(funcStates, e)
			luaK_freeexp(funcStates, e)
			e.info = luaK_codeABC(funcStates, "OP_NOT", 0, e.info, 0)
			e.k = "VRELOCABLE"
		else
			lua_assert(0) -- cannot happen
		end
		-- interchange true and false lists
		e.f, e.t = e.t, e.f
		luaK_removevalues(funcStates, e.f)
		luaK_removevalues(funcStates, e.t)
	end

	-- * used in (lparser) parserfield(), parserprimaryexp()

	local function luaK_indexed(funcStates, t, k)
		t.aux = luaK_exp2RK(funcStates, k)
		t.k = "VINDEXED"
	end

	-- * used only in luaK_codearith()

	local function luaK_constfolding(op, e1, e2)
		local r
		if not luaK_isnumeral(e1) or not luaK_isnumeral(e2) then
			return false
		end
		local v1 = e1.nval
		local v2 = e2.nval
		if op == "OP_ADD" then
			r = v1 + v2
		elseif op == "OP_SUB" then
			r = v1 - v2
		elseif op == "OP_MUL" then
			r = v1 * v2
		elseif op == "OP_DIV" then
			if v2 == 0 then
				return false
			end -- do not attempt to divide by 0
			r = v1 / v2
		elseif op == "OP_MOD" then
			if v2 == 0 then
				return false
			end -- do not attempt to divide by 0
			r = v1 % v2
		elseif op == "OP_POW" then
			r = v1 ^ v2
		elseif op == "OP_UNM" then
			r = -v1
		elseif op == "OP_LEN" then
			return false -- no constant folding for 'len'
		else
			lua_assert(0)
			r = 0
		end
		if luaK_numisnan(r) then
			return false
		end -- do not attempt to produce NaN
		e1.nval = r
		return true
	end

	-- * used in luaK_prefix(), luaK_posfix()

	local function luaK_codearith(funcStates, op, e1, e2)
		if luaK_constfolding(op, e1, e2) then
			return
		else
			local o2 = (op ~= "OP_UNM" and op ~= "OP_LEN") and luaK_exp2RK(funcStates, e2) or 0
			local o1 = luaK_exp2RK(funcStates, e1)
			if o1 > o2 then
				luaK_freeexp(funcStates, e1)
				luaK_freeexp(funcStates, e2)
			else
				luaK_freeexp(funcStates, e2)
				luaK_freeexp(funcStates, e1)
			end
			e1.info = luaK_codeABC(funcStates, op, 0, o1, o2)
			e1.k = "VRELOCABLE"
		end
	end

	-- * used only in luaK_posfix()

	local function luaK_codecomp(funcStates, op, cond, e1, e2)
		local o1 = luaK_exp2RK(funcStates, e1)
		local o2 = luaK_exp2RK(funcStates, e2)
		luaK_freeexp(funcStates, e2)
		luaK_freeexp(funcStates, e1)
		if cond == 0 and op ~= "OP_EQ" then
			-- exchange args to replace by `<' or `<='
			o1, o2 = o2, o1 -- o1 <==> o2
			cond = 1
		end
		e1.info = luaK_condjump(funcStates, op, cond, o1, o2)
		e1.k = "VJMP"
	end

	-- * used only in (lparser) parsersubexpr()

	local function luaK_prefix(funcStates, op, e)
		local e2 = {} -- expdesc
		e2.t, e2.f = luaK_NO_JUMP, luaK_NO_JUMP
		e2.k = "VKNUM"
		e2.nval = 0
		if op == "OPR_MINUS" then
			if not luaK_isnumeral(e) then
				luaK_exp2anyreg(funcStates, e) -- cannot operate on non-numeric constants
			end
			luaK_codearith(funcStates, "OP_UNM", e, e2)
		elseif op == "OPR_NOT" then
			luaK_codenot(funcStates, e)
		elseif op == "OPR_LEN" then
			luaK_exp2anyreg(funcStates, e) -- cannot operate on constants
			luaK_codearith(funcStates, "OP_LEN", e, e2)
		else
			lua_assert(0)
		end
	end

	-- * used only in (lparser) parsersubexpr()

	local function luaK_infix(funcStates, op, v)
		if op == "OPR_AND" then
			luaK_goiftrue(funcStates, v)
		elseif op == "OPR_OR" then
			luaK_goiffalse(funcStates, v)
		elseif op == "OPR_CONCAT" then
			luaK_exp2nextreg(funcStates, v) -- operand must be on the 'stack'
		elseif
			op == "OPR_ADD"
			or op == "OPR_SUB"
			or op == "OPR_MUL"
			or op == "OPR_DIV"
			or op == "OPR_MOD"
			or op == "OPR_POW"
		then
			if not luaK_isnumeral(v) then
				luaK_exp2RK(funcStates, v)
			end
		else
			luaK_exp2RK(funcStates, v)
		end
	end

	local function luaK_posfix(funcStates, op, e1, e2)
		-- needed because e1 = e2 doesn't copy values...
		-- * in 5.0.x, only k/info/aux/t/f copied, t for AND, f for OR
		--   but here, all elements are copied for completeness' sake
		local function copyexp(e1, e2)
			e1.k = e2.k
			e1.info = e2.info
			e1.aux = e2.aux
			e1.nval = e2.nval
			e1.t = e2.t
			e1.f = e2.f
		end
		if op == "OPR_AND" then
			lua_assert(e1.t == luaK_NO_JUMP) -- list must be closed
			luaK_dischargeVars(funcStates, e2)
			e2.f = luaK_concat(funcStates, e2.f, e1.f)
			copyexp(e1, e2)
		elseif op == "OPR_OR" then
			lua_assert(e1.f == luaK_NO_JUMP) -- list must be closed
			luaK_dischargeVars(funcStates, e2)
			e2.t = luaK_concat(funcStates, e2.t, e1.t)
			copyexp(e1, e2)
		elseif op == "OPR_CONCAT" then
			luaK_exp2val(funcStates, e2)
			if e2.k == "VRELOCABLE" and luaP_GET_OPCODE(luaK_getcode(funcStates, e2)) == "OP_CONCAT" then
				lua_assert(e1.info == luaK_getcode(funcStates, e2).B - 1)
				luaK_freeexp(funcStates, e1)
				luaK_getcode(funcStates, e2).B = e1.info
				e1.k = "VRELOCABLE"
				e1.info = e2.info
			else
				luaK_exp2nextreg(funcStates, e2) -- operand must be on the 'stack'
				luaK_codearith(funcStates, "OP_CONCAT", e1, e2)
			end
		else
			-- the following uses a table lookup in place of conditionals
			local arith = luaK_arith_op[op]
			if arith then
				luaK_codearith(funcStates, arith, e1, e2)
			else
				local comp = luaK_comp_op[op]
				if comp then
					luaK_codecomp(funcStates, comp, luaK_comp_cond[op], e1, e2)
				else
					lua_assert(0)
				end
			end --if arith
		end --if op
	end

	-- adjusts debug information for last instruction written, in order to
	-- change the line where item comes into existence
	-- * used in (lparser) parserfuncargs(), parserforbody(), parserfuncstat()

	local function luaK_fixline(funcStates, line)
		funcStates.f.lineinfo[funcStates.pc - 1] = line
	end

	-- general function to write an instruction into the instruction buffer,
	-- sets debug information too
	-- * used in luaK_codeABC(), luaK_codeABx()
	-- * called directly by (lparser) parserwhilestat()

	local function luaK_code(funcStates, i, line)
		local f = funcStates.f
		luaK_dischargejpc(funcStates) -- 'pc' will change
		-- put new instruction in code array
		parsergrowvector(funcStates.pc, parserMAX_INT, "code size overflow")
		f.code[funcStates.pc] = i
		-- save corresponding line information
		parsergrowvector(funcStates.pc, parserMAX_INT, "code size overflow")
		f.lineinfo[funcStates.pc] = line
		local pc = funcStates.pc
		funcStates.pc = funcStates.pc + 1
		return pc
	end

	-- writes an instruction of type ABC
	-- * calls luaK_code()

	function luaK_codeABC(funcStates, o, a, b, c)
		lua_assert(luaP_getOpMode(o) == luaP_OpMode.iABC)
		lua_assert(luaP_getBMode(o) ~= luaP_OpArgMask.OpArgN or b == 0)
		lua_assert(luaP_getCMode(o) ~= luaP_OpArgMask.OpArgN or c == 0)
		return luaK_code(funcStates, luaP_CREATE_ABC(o, a, b, c), lexerState_lastLine)
	end

	-- writes an instruction of type ABx
	-- * calls luaK_code(), called by luaK_codeAsBx()

	function luaK_codeABx(funcStates, o, a, bc)
		lua_assert(luaP_getOpMode(o) == luaP_OpMode.iABx or luaP_getOpMode(o) == luaP_OpMode.iAsBx)
		lua_assert(luaP_getCMode(o) == luaP_OpArgMask.OpArgN)
		return luaK_code(funcStates, luaP_CREATE_ABx(o, a, bc), lexerState_lastLine)
	end

	-- * used in (lparser) parsercloselistfield(), parserLastListField()

	local function luaK_setList(funcStates, base, nElems, tostore)
		local c = math_floor((nElems - 1) / luaP_LFIELDS_PER_FLUSH) + 1
		local b = (tostore == parserLUA_MULTRET) and 0 or tostore
		lua_assert(tostore ~= 0)
		if c <= luaP_MAXARG_C then
			luaK_codeABC(funcStates, "OP_SETLIST", base, b, c)
		else
			luaK_codeABC(funcStates, "OP_SETLIST", base, b, 0)
			luaK_code(funcStates, luaP_CREATE_Inst(c), lexerState_lastLine)
		end
		funcStates.freereg = base + 1 -- free registers with list values
	end

	-- this is a stripped-down luaM_growvector (from lmem.h) which is a
	-- macro based on luaM_growaux (in lmem.c); all the following does is
	-- reproduce the size limit checking logic of the original function
	-- so that error behaviour is identical
	-- * set the t field to nil, since this originally does a sizeof(t)
	-- * size (originally a pointer) is never updated, their final values
	--   are set by parserclose_func(), so overall things should still work

	function parsergrowvector(nElems, limit, e)
		if nElems >= limit then
			error(e) -- was luaG_runerror
		end
	end

	-- initialize a new function prototype structure (from lfunc.c)
	-- * used only in open_func()

	local function parserNewProto(L)
		return {
			k = {},
			sizek = 0,
			p = {},
			sizep = 0,
			code = {},
			sizecode = 0,
			sizelineinfo = 0,
			sizeupvalues = 0,
			nups = 0,
			upvalues = {},
			numParams = 0,
			isVararg = 0,
			maxStackSize = 0,
			lineinfo = {},
			sizelocalvars = 0,
			localvars = {},
			lineDefined = 0,
			lastLineDefined = 0,
			source = nil,
		}
	end

	--[[----
	-- parser functions
	------]]

	-- convenience function to access active local i, returns entry

	local function parsergetlocalvar(funcStates, i)
		return funcStates.f.localvars[funcStates.activeVar[i]]
	end

	-- prepares error message for display, for limits exceeded
	-- * used only in checklimit()

	local function parsererrorlimit(funcStates, limit, what)
		local msg = (funcStates.f.linedefined == 0) and "main function has more than " .. limit .. " " .. what
			or "function at line " .. funcStates.f.linedefined .. " has more than " .. limit .. " " .. what
		lexer_lexerror(msg, 0)
	end

	-- check a limit, string m provided as an error message

	local function parserchecklimit(funcStates, v, l, m)
		if v > l then
			parsererrorlimit(funcStates, l, m)
		end
	end

	--[[----
	-- nodes for block list (list of active blocks)
	-- struct BlockCnt:
	--   previous  -- chain (table: BlockCnt)
	--   breaklist  -- list of jumps out of this loop
	--   nactvar  -- # active local variables outside the breakable structure
	--   upval  -- true if some variable in the block is an upvalue (boolean)
	--   isBreakable  -- true if 'block' is a loop (boolean)
	------]]

	-- prototypes for recursive non-terminal functions

	-- prototypes deleted; not required in Lua

	-- throws a syntax error if token expected is not there

	local function parsererror_expected(token)
		lexer_syntaxerror(quote(lexer_token2str(token)) .. " expected")
	end

	-- tests for a token, returns outcome
	-- * return value changed to boolean

	local function parsertestnext(c)
		if lexerState_t.token == c then
			lexerNext()
			return true
		else
			return false
		end
	end

	-- check for existence of a token, throws error if not found

	local function parsercheck(c)
		if lexerState_t.token ~= c then
			parsererror_expected(c)
		end
	end

	-- verify existence of a token, then skip it

	local function parserCheckNext(c)
		parsercheck(c)
		lexerNext()
	end

	-- throws error if condition not matched

	local function parsercheck_condition(c, msg)
		if not c then
			lexer_syntaxerror(msg)
		end
	end

	-- verifies token conditions are met or else throw error

	local function parsercheck_match(what, who, where)
		if not parsertestnext(what) then
			if where == lexerState_lineNumber then
				parsererror_expected(what)
			else
				lexer_syntaxerror(
					quote(lexer_token2str(what))
						.. " expected (to close "
						.. quote(lexer_token2str(who))
						.. " at line "
						.. where
						.. ")"
				)
			end
		end
	end

	-- expect that token is a name, return the name

	local function parserstr_checkname()
		parsercheck("TK_NAME")
		local ts = lexerState_t.seminfo
		lexerNext()
		return ts
	end

	-- initialize a struct expdesc, expression description data structure

	local function parserInitExp(e, k, i)
		e.f, e.t = luaK_NO_JUMP, luaK_NO_JUMP
		e.k = k
		e.info = i
	end

	-- adds given string s in string pool, sets e as VK

	local function parsercodestring(e, s)
		parserInitExp(e, "VK", luaK_stringK(lexerState_funcstates, s))
	end

	-- consume a name token, adds it to string pool, sets e as VK

	local function parsercheckname(e)
		parsercodestring(e, parserstr_checkname())
	end

	-- creates struct entry for a local variable
	-- * used only in new_localvar()

	local function parserregisterlocalvar(varname)
		local funcStates = lexerState_funcstates
		local f = funcStates.f
		local nlocalvars = funcStates.nlocalvars

		parsergrowvector(nlocalvars, parserSHRT_MAX, "too many local variables")
		-- loop to initialize empty f.localvar positions not required
		f.localvars[nlocalvars] = { varname = varname } -- LocVar
		-- luaC_objbarrier(LuaState, f, varname) /* GC */
		funcStates.nlocalvars = nlocalvars + 1

		return nlocalvars
	end

	-- register a local variable, set in active variable list

	local function parsernew_localvar(name, n)
		local funcStates = lexerState_funcstates
		parserchecklimit(funcStates, funcStates.nactvar + n + 1, parserLUAI_MAXVARS, "local variables")
		funcStates.activeVar[funcStates.nactvar + n] = parserregisterlocalvar(name)
	end

	-- creates a new local variable given a name and an offuncstateset from nactvar
	-- * used in fornum(), forlist(), parlist(), body()

	local parsernew_localvarliteral = parsernew_localvar

	-- adds nVars number of new local variables, set debug information

	local function parseradjustlocalvars(nVars)
		local funcStates = lexerState_funcstates
		funcStates.nactvar = funcStates.nactvar + nVars
		for i = nVars, 1, -1 do
			parsergetlocalvar(funcStates, funcStates.nactvar - i).startpc = funcStates.pc
		end
	end

	-- removes a number of locals, set debug information

	local function parserremovevars(tolevel)
		local funcStates = lexerState_funcstates
		while funcStates.nactvar > tolevel do
			funcStates.nactvar = funcStates.nactvar - 1
			parsergetlocalvar(funcStates, funcStates.nactvar).endpc = funcStates.pc
		end
	end

	-- returns an existing upvalue index based on the given name, or
	-- creates a new upvalue struct entry and returns the new index
	-- * used only in singlevaraux()

	local function parserindexupvalue(funcStates, name, v)
		local f = funcStates.f
		for i = 0, f.nups - 1 do
			if funcStates.upvalues[i].k == v.k and funcStates.upvalues[i].info == v.info then
				lua_assert(f.upvalues[i] == name)
				return i
			end
		end
		-- new one
		parserchecklimit(funcStates, f.nups + 1, parserLUAI_MAXUPVALUES, "upvalues")
		parsergrowvector(f.nups, parserMAX_INT, "")
		-- loop to initialize empty f.upvalues positions not required
		f.upvalues[f.nups] = name
		-- luaC_objbarrier(funcStates->L, f, name); /* GC */
		lua_assert(v.k == "VLOCAL" or v.k == "VUPVAL")
		-- this is a partial copy; only k & info fields used
		funcStates.upvalues[f.nups] = { k = v.k, info = v.info }
		local nups = f.nups
		f.nups = f.nups + 1
		return nups
	end

	-- search the local variable namespace of the given funcStates for a match
	-- * used only in singlevaraux()

	local function parsersearchvar(funcStates, n)
		for i = funcStates.nactvar - 1, 0, -1 do
			if n == parsergetlocalvar(funcStates, i).varname then
				return i
			end
		end
		return -1 -- not found
	end

	-- * mark upvalue flags in function states up to a given level
	-- * used only in singlevaraux()

	local function parsermarkupval(funcStates, level)
		local bl = funcStates.bl
		while bl and bl.nactvar > level do
			bl = bl.previous
		end
		if bl then
			bl.upval = true
		end
	end

	-- handle locals, globals and upvalues and related processing
	-- * search mechanism is recursive, calls itself to search parents
	-- * used only in singlevar()

	local function parsersinglevaraux(funcStates, n, var, base)
		if funcStates == nil then -- no more levels?
			parserInitExp(var, "VGLOBAL", luaP_NO_REG) -- default is global variable
			return "VGLOBAL"
		else
			local v = parsersearchvar(funcStates, n) -- look up at current level
			if v >= 0 then
				parserInitExp(var, "VLOCAL", v)
				if base == 0 then
					parsermarkupval(funcStates, v) -- local will be used as an upval
				end
				return "VLOCAL"
			else -- not found at current level; try upper one
				if parsersinglevaraux(funcStates.prev, n, var, 0) == "VGLOBAL" then
					return "VGLOBAL"
				end
				var.info = parserindexupvalue(funcStates, n, var) -- else was LOCAL or UPVAL
				var.k = "VUPVAL" -- upvalue in this level
				return "VUPVAL"
			end --if v
		end --if funcStates
	end

	-- consume a name token, creates a variable (global|local|upvalue)
	-- * used in prefixexp(), funcname()

	local function parsersinglevar(var)
		local varname = parserstr_checkname()
		local funcStates = lexerState_funcstates
		if parsersinglevaraux(funcStates, varname, var, 1) == "VGLOBAL" then
			var.info = luaK_stringK(funcStates, varname) -- info points to global name
		end
	end

	-- adjust RHS to match LHS in an assignment
	-- * used in assignment(), forlist(), localstat()

	local function parseradjust_assign(nVars, nExps, e)
		local funcStates = lexerState_funcstates
		local extra = nVars - nExps
		if parserhasmultret(e.k) then
			extra = extra + 1 -- includes call itself
			if extra <= 0 then
				extra = 0
			end
			luaK_setreturns(funcStates, e, extra) -- last exp. provides the difference
			if extra > 1 then
				luaK_reserveRegisters(funcStates, extra - 1)
			end
		else
			if e.k ~= "VVOID" then
				luaK_exp2nextreg(funcStates, e)
			end -- close last expression
			if extra > 0 then
				local reg = funcStates.freereg
				luaK_reserveRegisters(funcStates, extra)
				luaK__nil(funcStates, reg, extra)
			end
		end
	end

	-- tracks and limits parsing depth, lua_assert check at end of parsing

	local function parserenterlevel()
		LuaState.nCcalls = LuaState.nCcalls + 1
		if LuaState.nCcalls > parserLUAI_MAXCCALLS then
			lexer_lexerror("chunk has too many syntax levels", 0)
		end
	end

	-- tracks parsing depth, a pair with parserenterlevel()

	local function parserleavelevel()
		LuaState.nCcalls = LuaState.nCcalls - 1
	end

	-- enters a code unit, initializes elements

	local function parserenterblock(funcStates, bl, isBreakable)
		bl.breaklist = luaK_NO_JUMP
		bl.isBreakable = isBreakable
		bl.nactvar = funcStates.nactvar
		bl.upval = false
		bl.previous = funcStates.bl
		funcStates.bl = bl
		lua_assert(funcStates.freereg == funcStates.nactvar)
	end

	-- leaves a code unit, close any upvalues

	local function parserLeaveBlock(funcStates)
		local bl = funcStates.bl
		funcStates.bl = bl.previous
		parserremovevars(bl.nactvar)
		if bl.upval then
			luaK_codeABC(funcStates, "OP_CLOSE", bl.nactvar, 0, 0)
		end
		-- a block either controls scope or breaks (never both)
		lua_assert(not bl.isBreakable or not bl.upval)
		lua_assert(bl.nactvar == funcStates.nactvar)
		funcStates.freereg = funcStates.nactvar -- free registers
		luaK_patchtohere(funcStates, bl.breaklist)
	end

	-- implement the instantiation of a function prototype, append list of
	-- upvalues after the instantiation instruction
	-- * used only in body()

	local function parserPushClosure(func, v)
		local funcStates = lexerState_funcstates
		local f = funcStates.f
		parsergrowvector(funcStates.np, luaP_MAXARG_Bx, "constant table overflow")
		-- loop to initialize empty f.p positions not required
		f.p[funcStates.np] = func.f
		funcStates.np = funcStates.np + 1
		-- luaC_objbarrier(lexerState->L, f, func->f); /* C */
		parserInitExp(v, "VRELOCABLE", luaK_codeABx(funcStates, "OP_CLOSURE", 0, funcStates.np - 1))
		for i = 0, func.f.nups - 1 do
			local o = (func.upvalues[i].k == "VLOCAL") and "OP_MOVE" or "OP_GETUPVAL"
			luaK_codeABC(funcStates, o, 0, func.upvalues[i].info, 0)
		end
	end

	-- opening of a function

	local function parserOpenFunc(funcStates)
		local L = LuaState
		local f = parserNewProto(LuaState)
		funcStates.f = f
		funcStates.prev = lexerState_funcstates -- linked list of funcStates
		funcStates.L = L
		lexerState_funcstates = funcStates
		funcStates.pc = 0
		funcStates.lasttarget = -1
		funcStates.jpc = luaK_NO_JUMP
		funcStates.freereg = 0
		funcStates.nk = 0
		funcStates.np = 0
		funcStates.nlocalvars = 0
		funcStates.nactvar = 0
		funcStates.bl = nil
		f.source = lexerState_source
		f.maxStackSize = 2 -- registers 0/1 are always valid
		funcStates.h = {} -- constant table; was luaH_new call
		-- anchor table of constants and prototype (to avoid being collected)
		-- sethvalue2s(L, L->top, funcStates->h); incr_top(L); /* C */
		-- setptvalue2s(L, L->top, f); incr_top(L);
	end

	-- closing of a function

	local function parserclose_func()
		local funcStates = lexerState_funcstates
		local f = funcStates.f
		parserremovevars(0)
		luaK_ret(funcStates, 0, 0) -- final return
		-- luaM_reallocvector deleted for f->code, f->lineinfo, f->k, f->p,
		-- f->localvars, f->upvalues; not required for Lua table arrays
		f.sizecode = funcStates.pc
		f.sizelineinfo = funcStates.pc
		f.sizek = funcStates.nk
		f.sizep = funcStates.np
		f.sizelocalvars = funcStates.nlocalvars
		f.sizeupvalues = f.nups
		--lua_assert(luaG_checkcode(f))  -- currently not implemented
		lua_assert(funcStates.bl == nil)
		lexerState_funcstates = funcStates.prev
	end

	--[[----
	-- GRAMMAR RULES
	------]]

	-- parse a function name suffix, for function call specifications
	-- * used in primaryexp(), funcname()

	local function parserfield(v)
		-- field -> ['.' | ':'] NAME
		local funcStates = lexerState_funcstates
		local key = {} -- expdesc
		luaK_exp2anyreg(funcStates, v)
		lexerNext() -- skip the dot or colon
		parsercheckname(key)
		luaK_indexed(funcStates, v, key)
	end

	-- parse a table indexing suffix, for constructors, expressions
	-- * used in recfield(), primaryexp()

	local function parseryindex(v)
		-- index -> '[' expr ']'
		lexerNext() -- skip the '['
		parserexpr(v)
		luaK_exp2val(lexerState_funcstates, v)
		parserCheckNext("]")
	end

	--[[----
	-- Rules for Constructors
	------]]
	--[[----
	-- struct ConsControl:
	--   v  -- last list item read (table: struct expdesc)
	--   t  -- table descriptor (table: struct expdesc)
	--   nh  -- total number of 'record' elements
	--   na  -- total number of array elements
	--   tostore  -- number of array elements pending to be stored
	------]]

	-- parse a table record (hash) field
	-- * used in constructor()

	local function parserRecField(cc)
		-- recfield -> (NAME | '['exp1']') = exp1
		local funcStates = lexerState_funcstates
		local reg = lexerState_funcstates.freereg
		local key, val = {}, {} -- expdesc
		if lexerState_t.token == "TK_NAME" then
			parserchecklimit(funcStates, cc.nh, parserMAX_INT, "items in a constructor")
			parsercheckname(key)
		else -- lexerState->t.token == '['
			parseryindex(key)
		end
		cc.nh = cc.nh + 1
		parserCheckNext("=")
		local rkkey = luaK_exp2RK(funcStates, key)
		parserexpr(val)
		luaK_codeABC(funcStates, "OP_SETTABLE", cc.t.info, rkkey, luaK_exp2RK(funcStates, val))
		funcStates.freereg = reg -- free registers
	end

	-- emit a set list instruction if enough elements (LFIELDS_PER_FLUSH)
	-- * used in constructor()

	local function parsercloselistfield(funcStates, cc)
		if cc.v.k == "VVOID" then
			return
		end -- there is no list item
		luaK_exp2nextreg(funcStates, cc.v)
		cc.v.k = "VVOID"
		if cc.tostore == luaP_LFIELDS_PER_FLUSH then
			luaK_setList(funcStates, cc.t.info, cc.na, cc.tostore) -- flush
			cc.tostore = 0 -- no more items pending
		end
	end

	-- emit a set list instruction at the end of parsing list constructor
	-- * used in constructor()

	local function parserLastListField(funcStates, cc)
		if cc.tostore == 0 then
			return
		end
		if parserhasmultret(cc.v.k) then
			luaK_setmultret(funcStates, cc.v)
			luaK_setList(funcStates, cc.t.info, cc.na, parserLUA_MULTRET)
			cc.na = cc.na - 1 -- do not count last expression (unknown number of elements)
		else
			if cc.v.k ~= "VVOID" then
				luaK_exp2nextreg(funcStates, cc.v)
			end
			luaK_setList(funcStates, cc.t.info, cc.na, cc.tostore)
		end
	end

	-- parse a table list (array) field
	-- * used in constructor()

	local function parserListField(cc)
		parserexpr(cc.v)
		parserchecklimit(lexerState_funcstates, cc.na, parserMAX_INT, "items in a constructor")
		cc.na = cc.na + 1
		cc.tostore = cc.tostore + 1
	end

	-- parse a table constructor
	-- * used in funcargs(), simpleexp()

	local function parserConstructor(t)
		-- constructor -> '{' [ field { fieldsep field } [ fieldsep ] ] '}'
		-- field -> recfield | listfield
		-- fieldsep -> ',' | ';'
		local funcStates = lexerState_funcstates
		local line = lexerState_lineNumber
		local pc = luaK_codeABC(funcStates, "OP_NEWTABLE", 0, 0, 0)
		local cc = {} -- ConsControl
		cc.v = {}
		cc.na, cc.nh, cc.tostore = 0, 0, 0
		cc.t = t
		parserInitExp(t, "VRELOCABLE", pc)
		parserInitExp(cc.v, "VVOID", 0) -- no value (yet)
		luaK_exp2nextreg(lexerState_funcstates, t) -- fix it at stack top (for gc)
		parserCheckNext("{")
		repeat
			lua_assert(cc.v.k == "VVOID" or cc.tostore > 0)
			if lexerState_t.token == "}" then
				break
			end
			parsercloselistfield(funcStates, cc)
			local c = lexerState_t.token

			if c == "TK_NAME" then -- may be listfields or recfields
				lexer_lookahead()
				if lexerState_lookahead.token ~= "=" then -- expression?
					parserListField(cc)
				else
					parserRecField(cc)
				end
			elseif c == "[" then -- constructor_item -> recfield
				parserRecField(cc)
			else -- constructor_part -> listfield
				parserListField(cc)
			end
		until not parsertestnext(",") and not parsertestnext(";")
		parsercheck_match("}", "{", line)
		parserLastListField(funcStates, cc)
		funcStates.f.code[pc].B = parserint2fb(cc.na) -- set initial array size
		funcStates.f.code[pc].C = parserint2fb(cc.nh) -- set initial table size
	end

	-- }======================================================================

	-- parse the arguments (parameters) of a function declaration
	-- * used in body()

	local function parserparlist()
		-- parlist -> [ param { ',' param } ]
		local funcStates = lexerState_funcstates
		local f = funcStates.f
		local nparams = 0
		f.isVararg = 0
		if lexerState_t.token ~= ")" then -- is 'parlist' not empty?
			repeat
				local c = lexerState_t.token
				if c == "TK_NAME" then -- param -> NAME
					parsernew_localvar(parserstr_checkname(), nparams)
					nparams = nparams + 1
				elseif c == "TK_DOTS" then -- param -> `...'
					lexerNext()
					-- [[
					-- #if defined(LUA_COMPAT_VARARG)
					-- use `arg' as default name
					parsernew_localvarliteral("arg", nparams)
					nparams = nparams + 1
					f.isVararg = parserVARARG_HASARG + parserVARARG_NEEDSARG
					-- #endif
					--]]
					f.isVararg = f.isVararg + parserVARARG_ISVARARG
				else
					lexer_syntaxerror("<name> or " .. quote("...") .. " expected")
				end
			until f.isVararg ~= 0 or not parsertestnext(",")
		end --if
		parseradjustlocalvars(nparams)
		-- NOTE: the following works only when HASARG_MASK is 2!
		f.numParams = funcStates.nactvar - (f.isVararg % parserHASARG_MASK)
		luaK_reserveRegisters(funcStates, funcStates.nactvar) -- reserve register for parameters
	end

	-- parse function declaration body
	-- * used in simpleexp(), localfunc(), funcstat()

	local function parseBody(e, needself, line)
		-- body ->  '(' parlist ')' chunk END
		local new_funcstate = {
			upvalues = {},
			activeVar = {},
			f = nil,
		}
		parserOpenFunc(new_funcstate)
		new_funcstate.f.lineDefined = line
		parserCheckNext("(")
		if needself then
			parsernew_localvarliteral("self", 0)
			parseradjustlocalvars(1)
		end
		parserparlist()
		parserCheckNext(")")
		parserchunk()
		new_funcstate.f.lastLineDefined = lexerState_lineNumber
		parsercheck_match("TK_END", "TK_FUNCTION", line)
		parserclose_func()
		parserPushClosure(new_funcstate, e)
	end

	-- parse a list of comma-separated expressions
	-- * used is multiple locations

	local function parserexplist1(v)
		-- explist1 -> expr { ',' expr }
		local n = 1 -- at least one expression
		parserexpr(v)
		while parsertestnext(",") do
			luaK_exp2nextreg(lexerState_funcstates, v)
			parserexpr(v)
			n = n + 1
		end
		return n
	end

	-- parse the parameters of a function call
	-- * contrast with parlist(), used in function declarations
	-- * used in primaryexp()

	local function parserfuncargs(f)
		local funcStates = lexerState_funcstates
		local args = {} -- expdesc
		local nparams
		local line = lexerState_lineNumber
		local c = lexerState_t.token
		if c == "(" then -- funcargs -> '(' [ explist1 ] ')'
			if line ~= lexerState_lastLine then
				lexer_syntaxerror("ambiguous syntax (function call x new statement)")
			end
			lexerNext()
			if lexerState_t.token == ")" then -- arg list is empty?
				args.k = "VVOID"
			else
				parserexplist1(args)
				luaK_setmultret(funcStates, args)
			end
			parsercheck_match(")", "(", line)
		elseif c == "{" then -- funcargs -> constructor
			parserConstructor(args)
		elseif c == "TK_STRING" then -- funcargs -> STRING
			parsercodestring(args, lexerState_t.seminfo)
			lexerNext() -- must use 'seminfo' before 'next'
		else
			lexer_syntaxerror("function arguments expected")
			return
		end
		lua_assert(f.k == "VNONRELOC")
		local base = f.info -- base register for call
		if parserhasmultret(args.k) then
			nparams = parserLUA_MULTRET -- open call
		else
			if args.k ~= "VVOID" then
				luaK_exp2nextreg(funcStates, args) -- close last argument
			end
			nparams = funcStates.freereg - (base + 1)
		end
		parserInitExp(f, "VCALL", luaK_codeABC(funcStates, "OP_CALL", base, nparams + 1, 2))
		luaK_fixline(funcStates, line)
		funcStates.freereg = base + 1 -- call remove function and arguments and leaves
		-- (unless changed) one result
	end

	--[[----
	-- Expression parsing
	------]]

	-- parses an expression in parentheses or a single variable
	-- * used in primaryexp()

	local function parserPrefixExp(v)
		-- prefixexp -> NAME | '(' expr ')'
		local c = lexerState_t.token
		if c == "(" then
			local line = lexerState_lineNumber
			lexerNext()
			parserexpr(v)
			parsercheck_match(")", "(", line)
			luaK_dischargeVars(lexerState_funcstates, v)
		elseif c == "TK_NAME" then
			parsersinglevar(v)
		else
			lexer_syntaxerror("unexpected symbol")
		end --if c
		return
	end

	-- parses a prefixexp (an expression in parentheses or a single variable)
	-- or a function call specification
	-- * used in simpleexp(), assignment(), exprstat()

	local function parserprimaryexp(v)
		-- primaryexp ->
		--    prefixexp { '.' NAME | '[' exp ']' | ':' NAME funcargs | funcargs }
		local funcStates = lexerState_funcstates
		parserPrefixExp(v)
		while true do
			local c = lexerState_t.token
			if c == "." then -- field
				parserfield(v)
			elseif c == "[" then -- '[' exp1 ']'
				local key = {} -- expdesc
				luaK_exp2anyreg(funcStates, v)
				parseryindex(key)
				luaK_indexed(funcStates, v, key)
			elseif c == ":" then -- ':' NAME funcargs
				local key = {} -- expdesc
				lexerNext()
				parsercheckname(key)
				luaK__self(funcStates, v, key)
				parserfuncargs(v)
			elseif c == "(" or c == "TK_STRING" or c == "{" then -- funcargs
				luaK_exp2nextreg(funcStates, v)
				parserfuncargs(v)
			else
				return
			end --if c
		end --while
	end

	-- parses general expression types, constants handled here
	-- * used in subexpr()

	local function parsersimpleexp(v)
		-- simpleexp -> NUMBER | STRING | NIL | TRUE | FALSE | ... |
		--              constructor | FUNCTION body | primaryexp
		local c = lexerState_t.token
		if c == "TK_NUMBER" then
			parserInitExp(v, "VKNUM", 0)
			v.nval = lexerState_t.seminfo
		elseif c == "TK_STRING" then
			parsercodestring(v, lexerState_t.seminfo)
		elseif c == "TK_NIL" then
			parserInitExp(v, "VNIL", 0)
		elseif c == "TK_TRUE" then
			parserInitExp(v, "VTRUE", 0)
		elseif c == "TK_FALSE" then
			parserInitExp(v, "VFALSE", 0)
		elseif c == "TK_DOTS" then -- vararg
			local funcStates = lexerState_funcstates
			parsercheck_condition(
				funcStates.f.isVararg ~= 0,
				"cannot use " .. quote("...") .. " outside a vararg function"
			)
			-- NOTE: the following substitutes for a bitop, but is value-specific
			local isVararg = funcStates.f.isVararg
			if isVararg >= parserVARARG_NEEDSARG then
				funcStates.f.isVararg = isVararg - parserVARARG_NEEDSARG -- don't need 'arg'
			end
			parserInitExp(v, "VVARARG", luaK_codeABC(funcStates, "OP_VARARG", 0, 1, 0))
		elseif c == "{" then -- constructor
			parserConstructor(v)
			return
		elseif c == "TK_FUNCTION" then
			lexerNext()
			parseBody(v, false, lexerState_lineNumber)
			return
		else
			parserprimaryexp(v)
			return
		end --if c
		lexerNext()
	end

	local function parsersubexpr(v, limit)
		parserenterlevel()
		local uop = parsergetunopr(lexerState_t.token)
		if uop ~= "OPR_NOUNOPR" then
			lexerNext()
			parsersubexpr(v, parserUNARY_PRIORITY)
			luaK_prefix(lexerState_funcstates, uop, v)
		else
			parsersimpleexp(v)
		end
		-- expand while operators have priorities higher than 'limit'
		local op = parsergetbinopr(lexerState_t.token)
		while op ~= "OPR_NOBINOPR" and parserpriority[luaK_BinOpr[op] + 1][1] > limit do
			local v2 = {} -- expdesc
			lexerNext()
			luaK_infix(lexerState_funcstates, op, v)
			-- read sub-expression with higher priority
			local nextop = parsersubexpr(v2, parserpriority[luaK_BinOpr[op] + 1][2])
			luaK_posfix(lexerState_funcstates, op, v, v2)
			op = nextop
		end
		parserleavelevel()
		return op -- return first untreated operator
	end

	-- Expression parsing starts here. Function subexpr is entered with the
	-- left operator (which is non-existent) priority of -1, which is lower
	-- than all actual operators. Expr information is returned in parm v.
	-- * used in multiple locations

	function parserexpr(v)
		parsersubexpr(v, 0)
	end

	-- }====================================================================
	--[[----
	-- Rules for Statements
	------]]

	-- checks next token, used as a look-ahead
	-- * returns boolean instead of 0|1
	-- * used in retstat(), chunk()

	local function parserblock_follow(token)
		return token == "TK_ELSE"
			or token == "TK_ELSEIF"
			or token == "TK_END"
			or token == "TK_UNTIL"
			or token == "TK_EOS"
	end

	-- parse a code block or unit
	-- * used in multiple functions

	local function parserblock()
		-- block -> chunk
		local funcStates = lexerState_funcstates
		local bl = { breaklist = nil } -- BlockCnt
		parserenterblock(funcStates, bl, false)
		parserchunk()
		lua_assert(bl.breaklist == luaK_NO_JUMP)
		parserLeaveBlock(funcStates)
	end

	-- structure to chain all variables in the left-hand side of an
	-- assignment
	-- struct LHS_assign:
	--   prev  -- (table: struct LHS_assign)
	--   v  -- variable (global, local, upvalue, or indexed) (table: expdesc)

	-- check whether, in an assignment to a local variable, the local variable
	-- is needed in a previous assignment (to a table). If so, save original
	-- local value in a safe place and use this safe copy in the previous
	-- assignment.
	-- * used in assignment()

	local function parsercheck_conflict(lh, v)
		local funcStates = lexerState_funcstates
		local extra = funcStates.freereg -- eventual position to save local variable
		local conflict = false
		while lh do
			if lh.v.k == "VINDEXED" then
				if lh.v.info == v.info then -- conflict?
					conflict = true
					lh.v.info = extra -- previous assignment will use safe copy
				end
				if lh.v.aux == v.info then -- conflict?
					conflict = true
					lh.v.aux = extra -- previous assignment will use safe copy
				end
			end
			lh = lh.prev
		end
		if conflict then
			luaK_codeABC(funcStates, "OP_MOVE", funcStates.freereg, v.info, 0) -- make copy
			luaK_reserveRegisters(funcStates, 1)
		end
	end

	-- parse a variable assignment sequence
	-- * recursively called
	-- * used in exprstat()

	function parserAssignment(lh, nVars)
		local e = {} -- expdesc
		-- test was: VLOCAL <= lh->v.k && lh->v.k <= VINDEXED
		local c = lh.v.k
		parsercheck_condition(c == "VLOCAL" or c == "VUPVAL" or c == "VGLOBAL" or c == "VINDEXED", "syntax error")
		if parsertestnext(",") then -- assignment -> ',' primaryexp assignment
			local nv = {} -- LHS_assign
			nv.v = {}
			nv.prev = lh
			parserprimaryexp(nv.v)
			if nv.v.k == "VLOCAL" then
				parsercheck_conflict(lh, nv.v)
			end
			parserchecklimit(
				lexerState_funcstates,
				nVars,
				parserLUAI_MAXCCALLS - LuaState.nCcalls,
				"variables in assignment"
			)
			parserAssignment(nv, nVars + 1)
		else -- assignment -> '=' explist1
			parserCheckNext("=")
			local nExps = parserexplist1(e)
			if nExps ~= nVars then
				parseradjust_assign(nVars, nExps, e)
				if nExps > nVars then
					lexerState_funcstates.freereg = lexerState_funcstates.freereg - (nExps - nVars) -- remove extra values
				end
			else
				luaK_setoneret(lexerState_funcstates, e) -- close last expression
				luaK_storeVar(lexerState_funcstates, lh.v, e)
				return -- avoid default
			end
		end
		parserInitExp(e, "VNONRELOC", lexerState_funcstates.freereg - 1) -- default assignment
		luaK_storeVar(lexerState_funcstates, lh.v, e)
	end

	-- parse condition in a repeat statement or an if control structure
	-- * used in repeatstat(), test_then_block()

	local function parsercond()
		-- cond -> exp
		local v = { k = nil, f = nil } -- expdesc
		parserexpr(v) -- read condition
		if v.k == "VNIL" then
			v.k = "VFALSE"
		end -- 'falses' are all equal here
		luaK_goiftrue(lexerState_funcstates, v)
		return v.f
	end

	-- parse a break statement
	-- * used in statements()

	local function parserbreakstat()
		-- stat -> BREAK
		local funcStates = lexerState_funcstates
		local bl = funcStates.bl
		local upval = false
		while bl and not bl.isBreakable do
			if bl.upval then
				upval = true
			end
			bl = bl.previous
		end
		if not bl then
			lexer_syntaxerror("no loop to break")
		end
		if upval then
			luaK_codeABC(funcStates, "OP_CLOSE", bl.nactvar, 0, 0)
		end
		bl.breaklist = luaK_concat(funcStates, bl.breaklist, luaK_jump(funcStates))
	end

	-- parse a while-do control structure, body processed by block()
	-- * with dynamic array sizes, MAXEXPWHILE + EXTRAEXP limits imposed by
	--   the function's implementation can be removed
	-- * used in statements()

	local function parserwhilestat(line)
		-- whilestat -> WHILE cond DO block END
		local funcStates = lexerState_funcstates
		local bl = {} -- BlockCnt
		lexerNext() -- skip WHILE
		local whileinit = luaK_getLabel(funcStates)
		local condexit = parsercond()
		parserenterblock(funcStates, bl, true)
		parserCheckNext("TK_DO")
		parserblock()
		luaK_patchlist(funcStates, luaK_jump(funcStates), whileinit)
		parsercheck_match("TK_END", "TK_WHILE", line)
		parserLeaveBlock(funcStates)
		luaK_patchtohere(funcStates, condexit) -- false conditions finish the loop
	end

	-- parse a repeat-until control structure, body parsed by chunk()
	-- * used in statements()

	local function parserRepeatStatement(line)
		-- repeatstat -> REPEAT block UNTIL cond
		local funcStates = lexerState_funcstates
		local repeat_init = luaK_getLabel(funcStates)
		local bl1, bl2 = {}, { upval = nil } -- BlockCnt
		parserenterblock(funcStates, bl1, true) -- loop block
		parserenterblock(funcStates, bl2, false) -- scope block
		lexerNext() -- skip REPEAT
		parserchunk()
		parsercheck_match("TK_UNTIL", "TK_REPEAT", line)
		local condexit = parsercond() -- read condition (inside scope block)
		if not bl2.upval then -- no upvalues?
			parserLeaveBlock(funcStates) -- finish scope
			luaK_patchlist(lexerState_funcstates, condexit, repeat_init) -- close the loop
		else -- complete semantics when there are upvalues
			parserbreakstat() -- if condition then break
			luaK_patchtohere(lexerState_funcstates, condexit) -- else...
			parserLeaveBlock(funcStates) -- finish scope...
			luaK_patchlist(lexerState_funcstates, luaK_jump(funcStates), repeat_init) -- and repeat
		end
		parserLeaveBlock(funcStates) -- finish loop
	end

	-- parse the single expressions needed in numerical for loops
	-- * used in fornum()

	local function parserexp1()
		local expdesc = { k = nil }
		parserexpr(expdesc)
		local k = expdesc.k
		luaK_exp2nextreg(lexerState_funcstates, expdesc)
		return k
	end

	-- parse a for loop body for both versions of the for loop
	-- * used in fornum(), forlist()

	local function parserforbody(base, line, nVars, isnum)
		-- forbody -> DO block
		local bl = {} -- BlockCnt
		local funcStates = lexerState_funcstates
		parseradjustlocalvars(3) -- control variables
		parserCheckNext("TK_DO")
		local prep = isnum and luaK_codeAsBx(funcStates, "OP_FORPREP", base, luaK_NO_JUMP) or luaK_jump(funcStates)
		parserenterblock(funcStates, bl, false) -- scope for declared variables
		parseradjustlocalvars(nVars)
		luaK_reserveRegisters(funcStates, nVars)
		parserblock()
		parserLeaveBlock(funcStates) -- end of scope for declared variables
		luaK_patchtohere(funcStates, prep)
		local endfor = isnum and luaK_codeAsBx(funcStates, "OP_FORLOOP", base, luaK_NO_JUMP)
			or luaK_codeABC(funcStates, "OP_TFORLOOP", base, 0, nVars)
		luaK_fixline(funcStates, line) -- pretend that `OP_FOR' starts the loop
		luaK_patchlist(funcStates, isnum and endfor or luaK_jump(funcStates), prep + 1)
	end

	-- parse a numerical for loop, calls forbody()
	-- * used in forstat()

	local function parserfornum(varname, line)
		-- fornum -> NAME = exp1,exp1[,exp1] forbody
		local funcStates = lexerState_funcstates
		local base = funcStates.freereg
		parsernew_localvarliteral("(for index)", 0)
		parsernew_localvarliteral("(for limit)", 1)
		parsernew_localvarliteral("(for step)", 2)
		parsernew_localvar(varname, 3)
		parserCheckNext("=")
		parserexp1() -- initial value
		parserCheckNext(",")
		parserexp1() -- limit
		if parsertestnext(",") then
			parserexp1() -- optional step
		else -- default step = 1
			luaK_codeABx(funcStates, "OP_LOADK", funcStates.freereg, luaK_numberK(funcStates, 1))
			luaK_reserveRegisters(funcStates, 1)
		end
		parserforbody(base, line, 1, true)
	end

	-- parse a generic for loop, calls forbody()
	-- * used in forstat()

	local function parserforlist(indexname)
		-- forlist -> NAME {,NAME} IN explist1 forbody
		local funcStates = lexerState_funcstates
		local expdesc = {}
		local nVars = 0
		local base = funcStates.freereg
		-- create control variables
		parsernew_localvarliteral("(for generator)", nVars)
		nVars = nVars + 1
		parsernew_localvarliteral("(for state)", nVars)
		nVars = nVars + 1
		parsernew_localvarliteral("(for control)", nVars)
		nVars = nVars + 1
		-- create declared variables
		parsernew_localvar(indexname, nVars)
		nVars = nVars + 1
		while parsertestnext(",") do
			parsernew_localvar(parserstr_checkname(), nVars)
			nVars = nVars + 1
		end
		parserCheckNext("TK_IN")
		local line = lexerState_lineNumber
		parseradjust_assign(3, parserexplist1(expdesc), expdesc)
		luaK_checkstack(funcStates, 3) -- extra space to call generator
		parserforbody(base, line, nVars - 3, false)
	end

	-- initial parsing for a for loop, calls fornum() or forlist()
	-- * used in statements()

	local function parserForStatement(line)
		-- forstat -> FOR (fornum | forlist) END
		local funcStates = lexerState_funcstates
		local bl = {} -- BlockCnt
		parserenterblock(funcStates, bl, true) -- scope for loop and control variables
		lexerNext() -- skip `for'
		local varname = parserstr_checkname() -- first variable name
		local c = lexerState_t.token
		if c == "=" then
			parserfornum(varname, line)
		elseif c == "," or c == "TK_IN" then
			parserforlist(varname)
		else
			lexer_syntaxerror(quote("=") .. " or " .. quote("in") .. " expected")
		end
		parsercheck_match("TK_END", "TK_FOR", line)
		parserLeaveBlock(funcStates) -- loop scope (`break' jumps to this point)
	end

	-- parse part of an if control structure, including the condition
	-- * used in ifuncstatestat()

	local function parsertest_then_block()
		-- test_then_block -> [IF | ELSEIF] cond THEN block
		lexerNext() -- skip IF or ELSEIF
		local condexit = parsercond()
		parserCheckNext("TK_THEN")
		parserblock() -- `then' part
		return condexit
	end

	-- parse an if control structure
	-- * used in statements()

	local function parserifuncstatestat(line)
		-- ifuncstatestat -> IF cond THEN block {ELSEIF cond THEN block} [ELSE block] END
		local funcStates = lexerState_funcstates
		local escapelist = luaK_NO_JUMP
		local flist = parsertest_then_block() -- IF cond THEN block
		while lexerState_t.token == "TK_ELSEIF" do
			escapelist = luaK_concat(funcStates, escapelist, luaK_jump(funcStates))
			luaK_patchtohere(funcStates, flist)
			flist = parsertest_then_block() -- ELSEIF cond THEN block
		end
		if lexerState_t.token == "TK_ELSE" then
			escapelist = luaK_concat(funcStates, escapelist, luaK_jump(funcStates))
			luaK_patchtohere(funcStates, flist)
			lexerNext() -- skip ELSE (after patch, for correct line info)
			parserblock() -- 'else' part
		else
			escapelist = luaK_concat(funcStates, escapelist, flist)
		end
		luaK_patchtohere(funcStates, escapelist)
		parsercheck_match("TK_END", "TK_IF", line)
	end

	-- parse a local function statement
	-- * used in statements()

	local function parserlocalfunc()
		local v, b = {}, {} -- expdesc
		local funcStates = lexerState_funcstates
		parsernew_localvar(parserstr_checkname(), 0)
		parserInitExp(v, "VLOCAL", funcStates.freereg)
		luaK_reserveRegisters(funcStates, 1)
		parseradjustlocalvars(1)
		parseBody(b, false, lexerState_lineNumber)
		luaK_storeVar(funcStates, v, b)
		-- debug information will only see the variable after this point!
		parsergetlocalvar(funcStates, funcStates.nactvar - 1).startpc = funcStates.pc
	end

	-- parse a local variable declaration statement
	-- * used in statements()

	local function parserlocalstat()
		-- stat -> LOCAL NAME {',' NAME} ['=' explist1]
		local nVars = 0
		local nExps
		local expdesc = {}
		repeat
			parsernew_localvar(parserstr_checkname(), nVars)
			nVars = nVars + 1
		until not parsertestnext(",")
		if parsertestnext("=") then
			nExps = parserexplist1(expdesc)
		else
			expdesc.k = "VVOID"
			nExps = 0
		end
		parseradjust_assign(nVars, nExps, expdesc)
		parseradjustlocalvars(nVars)
	end

	-- parse a function name specification
	-- * used in funcstat()

	local function parserfuncname(v)
		-- funcname -> NAME {field} [':' NAME]
		parsersinglevar(v)
		while lexerState_t.token == "." do
			parserfield(v)
		end

		local needself = false
		if lexerState_t.token == ":" then
			needself = true
			parserfield(v)
		end
		return needself
	end

	-- parse a function statement
	-- * used in statements()

	local function parserfuncstat(line)
		-- funcstat -> FUNCTION funcname body
		local v, b = {}, {} -- expdesc
		lexerNext() -- skip FUNCTION
		local needself = parserfuncname(v)
		parseBody(b, needself, line)
		luaK_storeVar(lexerState_funcstates, v, b)
		luaK_fixline(lexerState_funcstates, line) -- definition 'happens' in the first line
	end

	-- parse a function call with no returns or an assignment statement
	-- * used in statements()

	local function parserexprstat()
		-- stat -> func | assignment
		local funcStates = lexerState_funcstates
		local v = {} -- LHS_assign
		v.v = {}
		parserprimaryexp(v.v)
		if v.v.k == "VCALL" then -- stat -> func
			luaK_getcode(funcStates, v.v).C = 1 -- call statement uses no results
		else -- stat -> assignment
			v.prev = nil
			parserAssignment(v, 1)
		end
	end

	-- parse a return statement
	-- * used in statements()

	local function parserretstat()
		-- stat -> RETURN explist
		local funcStates = lexerState_funcstates
		local e = { k = nil } -- expdesc
		local first, nret -- registers with returned values
		lexerNext() -- skip RETURN
		if parserblock_follow(lexerState_t.token) or lexerState_t.token == ";" then
			first, nret = 0, 0 -- return no values
		else
			nret = parserexplist1(e) -- optional return values
			if parserhasmultret(e.k) then
				luaK_setmultret(funcStates, e)
				if e.k == "VCALL" and nret == 1 then -- tail call?
					luaP_SET_OPCODE(luaK_getcode(funcStates, e), "OP_TAILCALL")
					lua_assert(luaK_getcode(funcStates, e).A == funcStates.nactvar)
				end
				first = funcStates.nactvar
				nret = parserLUA_MULTRET -- return all values
			else
				if nret == 1 then -- only one single value?
					first = luaK_exp2anyreg(funcStates, e)
				else
					luaK_exp2nextreg(funcStates, e) -- values must go to the 'stack'
					first = funcStates.nactvar -- return all 'active' values
					lua_assert(nret == funcStates.freereg - first)
				end
			end --if
		end --if
		luaK_ret(funcStates, first, nret)
	end

	-- initial parsing for statements, calls a lot of functions
	-- * returns boolean instead of 0|1
	-- * used in chunk()

	local function parserstatement()
		local line = lexerState_lineNumber -- may be needed for error messages
		local c = lexerState_t.token
		if c == "TK_IF" then -- stat -> ifuncstatestat
			parserifuncstatestat(line)
			return false
		elseif c == "TK_WHILE" then -- stat -> whilestat
			parserwhilestat(line)
			return false
		elseif c == "TK_DO" then -- stat -> DO block END
			lexerNext() -- skip DO
			parserblock()
			parsercheck_match("TK_END", "TK_DO", line)
			return false
		elseif c == "TK_FOR" then -- stat -> forstat
			parserForStatement(line)
			return false
		elseif c == "TK_REPEAT" then -- stat -> repeatstat
			parserRepeatStatement(line)
			return false
		elseif c == "TK_FUNCTION" then -- stat -> funcstat
			parserfuncstat(line)
			return false
		elseif c == "TK_LOCAL" then -- stat -> localstat
			lexerNext() -- skip LOCAL
			if parsertestnext("TK_FUNCTION") then -- local function?
				parserlocalfunc()
			else
				parserlocalstat()
			end
			return false
		elseif c == "TK_RETURN" then -- stat -> retstat
			parserretstat()
			return true -- must be last statement
		elseif c == "TK_BREAK" then -- stat -> breakstat
			lexerNext() -- skip BREAK
			parserbreakstat()
			return true -- must be last statement
		else
			parserexprstat()
			return false -- to avoid warnings
		end --if c
	end

	-- parse a chunk, which consists of a bunch of statements
	-- * used in parser(), body(), block(), repeatstat()

	function parserchunk()
		-- chunk -> { stat [';'] }
		local islast = false
		parserenterlevel()
		while not islast and not parserblock_follow(lexerState_t.token) do
			islast = parserstatement()
			parsertestnext(";")
			lua_assert(
				lexerState_funcstates.f.maxStackSize >= lexerState_funcstates.freereg
					and lexerState_funcstates.freereg >= lexerState_funcstates.nactvar
			)
			lexerState_funcstates.freereg = lexerState_funcstates.nactvar -- free registers
		end
		parserleavelevel()
	end

	lexerNextCharacter() -- read first char

	parserOpenFunc(funcstate)
	funcstate.f.isVararg = parserVARARG_ISVARARG -- main func. is always vararg
	lexerNext() -- read first token
	parserchunk()
	parsercheck("TK_EOS")
	parserclose_func()
	lua_assert(funcstate.prev == nil)
	lua_assert(funcstate.f.nups == 0)
	lua_assert(lexerState_funcstates == nil)
	local func = funcstate.f

	local buff, len = {}, 0

	local dumpState_strip = false
	--[[----
	-- Functions to make a binary chunk
	-- * many functions have the size parameter removed, since output is
	--   in the form of a string and some sizes are implicit or hard-coded
	------]]

	-- dumps a char
	local function luaU_DumpChar(y)
		len = len + 1
		buff[len] = string_char_t[y]
	end

	-- dumps a 32-bit signed or unsigned integer (for int) (hard-coded)
	local function luaU_DumpInt(x)
		len = len + 1
		buff[len] = luaU_from_int(x)
	end

	-- dumps a 32-bit signed or unsigned integer (for int) (hard-coded)
	local function luaU_DumpSizeT(x)
		len = len + 1
		buff[len] = luaU_from_int(x)

		if size_size_t == 8 then
			len = len + 1
			buff[len] = luaU_from_int(0)
		end
	end

	-- dumps a lua_Number (hard-coded as a double)
	local function luaU_DumpNumber(x)
		len = len + 1
		buff[len] = luaU_from_double(x)
	end

	-- dumps a Lua string (size type is hard-coded)
	local function luaU_DumpString(s)
		if s == nil then
			luaU_DumpSizeT(0)
		else
			s = s .. "\0" -- include trailing '\0'
			luaU_DumpSizeT(#s)
			len = len + 1
			buff[len] = s
		end
	end

	-- dumps instruction block from function prototype

	local function luaU_DumpCode(f)
		local n = f.sizecode
		--was DumpVector
		luaU_DumpInt(n)
		for i = 0, n - 1 do
			len = len + 1
			buff[len] = luaP_Instruction(f.code[i])
		end
	end

	-- dump debug information

	local function luaU_DumpDebug(f)
		local n = dumpState_strip and 0 or f.sizelineinfo -- dump line information
		--was DumpVector
		luaU_DumpInt(n)
		for i = 0, n - 1 do
			luaU_DumpInt(f.lineinfo[i])
		end
		local n = dumpState_strip and 0 or f.sizelocalvars -- dump local information
		luaU_DumpInt(n)
		for i = 0, n - 1 do
			luaU_DumpString(f.localvars[i].varname)
			luaU_DumpInt(f.localvars[i].startpc)
			luaU_DumpInt(f.localvars[i].endpc)
		end
		local n = dumpState_strip and 0 or f.sizeupvalues -- dump upvalue information
		luaU_DumpInt(n)
		for i = 0, n - 1 do
			luaU_DumpString(f.upvalues[i])
		end
	end

	-- dump constant pool from function prototype
	-- * bvalue(o), nvalue(o) and rawtsvalue(o) macros removed

	local luaU_DumpFunction
	local function luaU_DumpConstants(f)
		local n = f.sizek
		luaU_DumpInt(n)
		for i = 0, n - 1 do
			local o = f.k[i] -- TValue

			local tt = type(o.value)
			if tt == "number" then
				luaU_DumpChar(3)
				luaU_DumpNumber(o.value)
			elseif tt == "string" then
				luaU_DumpChar(4)
				luaU_DumpString(o.value)
			elseif tt == "nil" then
				luaU_DumpChar(0)
			elseif tt == "boolean" then
				luaU_DumpChar(1)
				luaU_DumpChar(o.value and 1 or 0)
			else
				luaU_DumpChar(-1) -- the rest should not appear
			end
		end
		n = f.sizep
		luaU_DumpInt(n)
		for i = 0, n - 1 do
			luaU_DumpFunction(f.p[i], f.source)
		end
	end

	-- dump child function prototypes from function prototype

	function luaU_DumpFunction(f, p)
		local source = f.source
		if source == p or dumpState_strip then
			source = nil
		end
		luaU_DumpString(source)
		luaU_DumpInt(f.lineDefined)
		luaU_DumpInt(f.lastLineDefined)
		luaU_DumpChar(f.nups)
		luaU_DumpChar(f.numParams)
		luaU_DumpChar(f.isVararg)
		luaU_DumpChar(f.maxStackSize)
		luaU_DumpCode(f)
		luaU_DumpConstants(f)
		luaU_DumpDebug(f)
	end

	-- dump header
	local x = 1
	local h = luaU_LUA_SIGNATURE
		.. string_char(
			luaU_LUAC_VERSION,
			luaU_LUAC_FORMAT,
			x, -- endianness (1=little)
			4, -- sizeof(int)
			size_size_t, -- sizeof(size_t)
			4, -- sizeof(Instruction)
			8, -- sizeof(lua_Number)
			0
		) -- is lua_Number integral?
	lua_assert(#h == luaU_LUAC_HEADERSIZE) -- fixed buffer now an lua_assert
	len = len + 1
	buff[len] = h

	-- dump function
	luaU_DumpFunction(func, nil)
	-- a string.dump equivalent in returned

	return table_concat(buff)
end