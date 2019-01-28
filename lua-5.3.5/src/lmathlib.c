/*
** $Id: lmathlib.c,v 1.119.1.1 2017/04/19 17:20:42 roberto Exp $
** Standard mathematical library
** See Copyright Notice in lua.h
*/

#define lmathlib_c
#define LUA_LIB

#include "lprefix.h"


#include <stdlib.h>
#include <math.h>

#include "lua.h"

#include "lauxlib.h"
#include "lualib.h"


#undef PI
#define PI	(l_mathop(3.141592653589793238462643383279502884))


#if !defined(l_rand)		/* { */
#if defined(LUA_USE_POSIX)
#define l_rand()	random()
#define l_srand(x)	srandom(x)
#define L_RANDMAX	2147483647	/* (2^31 - 1), following POSIX */
#else
#define l_rand()	rand()
#define l_srand(x)	srand(x)
#define L_RANDMAX	RAND_MAX
#endif
#endif				/* } */

/*
	求绝对值
		math_abs参数为一个lua栈，首先判断栈底数据是不是整数，是的话获取该值，如果是负数，用无符号0减去该值，并将结果压入栈中。
		如果是不是整数，则直接按实数处理，调用C函数fabs处理后压入栈，最后返回结果的数量1.
*/
static int math_abs(lua_State *L) {
	if (lua_isinteger(L, 1)) {
		lua_Integer n = lua_tointeger(L, 1);
		if (n < 0) n = (lua_Integer)(0u - (lua_Unsigned)n);
		lua_pushinteger(L, n);
	}
	else
		lua_pushnumber(L, l_mathop(fabs)(luaL_checknumber(L, 1)));
	return 1;
}
/*
	求sin函数(角度值)
*/
static int math_sin(lua_State *L) {
	lua_pushnumber(L, l_mathop(sin)(luaL_checknumber(L, 1))); //取得栈顶元素检测是不是number，然后求sin，最后再压入lua栈中
	return 1;
}
/*
	求cos函数(角度值)
*/
static int math_cos(lua_State *L) {
	lua_pushnumber(L, l_mathop(cos)(luaL_checknumber(L, 1)));
	return 1;
}
/*
	求tan函数(角度值)
*/
static int math_tan(lua_State *L) {
	lua_pushnumber(L, l_mathop(tan)(luaL_checknumber(L, 1)));
	return 1;
}
/*
	反正弦
*/
static int math_asin(lua_State *L) {
	lua_pushnumber(L, l_mathop(asin)(luaL_checknumber(L, 1)));
	return 1;
}
/*
	反余弦
*/
static int math_acos(lua_State *L) {
	lua_pushnumber(L, l_mathop(acos)(luaL_checknumber(L, 1)));
	return 1;
}
/*
	反正切
*/
static int math_atan(lua_State *L) {
	lua_Number y = luaL_checknumber(L, 1);
	lua_Number x = luaL_optnumber(L, 2, 1);
	lua_pushnumber(L, l_mathop(atan2)(y, x));
	return 1;
}

/*
	math_toint作用是把一个number转成整形并压入栈
	lua_tointegerx判断索引处的数值能否转为int，并将结果返回，返回信息付给vaild。
	不能够转换的话，向栈中压入一个nil
*/
static int math_toint(lua_State *L) {
	int valid;
	lua_Integer n = lua_tointegerx(L, 1, &valid);
	if (valid)
		lua_pushinteger(L, n);
	else {
		luaL_checkany(L, 1);
		lua_pushnil(L);  /* value is not convertible to integer */
	}
	return 1;
}


/*
	  把一个数值优先按照int类型压入栈
	  可以转化为int的话，就压入int
	  不可以的话就按照number的类型压入栈
*/
static void pushnumint(lua_State *L, lua_Number d) {
	lua_Integer n;
	if (lua_numbertointeger(d, &n))  /* does 'd' fit in an integer? */
		lua_pushinteger(L, n);  /* result is integer */
	else
		lua_pushnumber(L, d);  /* result is float */
}

/*
	向下取整
	  math_floor的作用是获取数值的整数部分，其实就是向下取整floor(4.5) 就是4
	  如果这个数值本身就是int的话，直接lua_settop就可以了（设置栈顶为索引1）
	  不是的话，就用C函数floor向下取整，然后将得出来的结果压入栈中。
*/
static int math_floor(lua_State *L) {
	if (lua_isinteger(L, 1))
		lua_settop(L, 1);  /* integer is its own floor */
	else {
		lua_Number d = l_mathop(floor)(luaL_checknumber(L, 1));
		pushnumint(L, d);
	}
	return 1;
}

/*
	向上取整
	  这个是向上取整ceil(4.5) 就是5
	  如果这个数值本身就是int的话，直接lua_settop就可以了（设置栈顶为索引1）
	  不是的话，就用C函数ceil向下取整，然后将得出来的结果压入栈中。
*/
static int math_ceil(lua_State *L) {
	if (lua_isinteger(L, 1))
		lua_settop(L, 1);  /* integer is its own ceil */
	else {
		lua_Number d = l_mathop(ceil)(luaL_checknumber(L, 1));
		pushnumint(L, d);
	}
	return 1;
}

/*
	取模运算
		fmod(14, 5) => 4
*/
static int math_fmod(lua_State *L) {
	if (lua_isinteger(L, 1) && lua_isinteger(L, 2)) {
		lua_Integer d = lua_tointeger(L, 2);
		if ((lua_Unsigned)d + 1u <= 1u) {  /* special cases: -1 or 0 */
			luaL_argcheck(L, d != 0, 2, "zero");
			lua_pushinteger(L, 0);  /* avoid overflow with 0x80000... / -1 */
		}
		else
			lua_pushinteger(L, lua_tointeger(L, 1) % d);
	}
	else
		lua_pushnumber(L, l_mathop(fmod)(luaL_checknumber(L, 1),
			luaL_checknumber(L, 2)));
	return 1;
}


/*
** next function does not use 'modf', avoiding problems with 'double*'
** (which is not compatible with 'float*') when lua_Number is not
** 'double'.
*/
/*
	求整数和小数
	  math_modf是把当前值的整数部分和小数部分分开，并返回
	  如果参数是整数的话，压进去一个0就可以了，当做小数部分
	  如果不是整数的话，通过判断该数值的正负，来进行获取小数部分，完成后压入栈中即可
*/
static int math_modf(lua_State *L) {
	if (lua_isinteger(L, 1)) {
		lua_settop(L, 1);  /* number is its own integer part */
		lua_pushnumber(L, 0);  /* no fractional part */
	}
	else {
		lua_Number n = luaL_checknumber(L, 1);
		/* integer part (rounds toward zero) */
		lua_Number ip = (n < 0) ? l_mathop(ceil)(n) : l_mathop(floor)(n);
		pushnumint(L, ip);
		/* fractional part (test needed for inf/-inf) */
		lua_pushnumber(L, (n == ip) ? l_mathop(0.0) : (n - ip));
	}
	return 2;
}


/*
  math_sqrt把一个数开平方
  调用C函数sqrt就可以了
*/
static int math_sqrt(lua_State *L) {
	lua_pushnumber(L, l_mathop(sqrt)(luaL_checknumber(L, 1)));
	return 1;
}


/*
  math_ult判断大小
  如果小于的话，返回一个true
*/
static int math_ult(lua_State *L) {
	lua_Integer a = luaL_checkinteger(L, 1);
	lua_Integer b = luaL_checkinteger(L, 2);
	lua_pushboolean(L, (lua_Unsigned)a < (lua_Unsigned)b);
	return 1;
}


/*
  math_log计算一个数字的自然对数
  首先获取这个数字，然后lua_isnoneornil判断这个数字如果是nil的话，返回true，这里要做这个判断的话，是默认处理以10为底的自然对数（就是只传一个参数）
  否则的话，按照规定的C语言版本来进行处理
  如果是C89协议的话，分别处理以10为底和其他底。如果不是的话就处理以2为底。
*/
static int math_log(lua_State *L) {
	lua_Number x = luaL_checknumber(L, 1);
	lua_Number res;
	if (lua_isnoneornil(L, 2))
		res = l_mathop(log)(x);
	else {
		lua_Number base = luaL_checknumber(L, 2);
#if !defined(LUA_USE_C89)
		if (base == l_mathop(2.0))
			res = l_mathop(log2)(x); else
#endif
			if (base == l_mathop(10.0))
				res = l_mathop(log10)(x);
			else
				res = l_mathop(log)(x) / l_mathop(log)(base);
	}
	lua_pushnumber(L, res);
	return 1;
}

/*
	把双精度数val分解为数字部分（尾数）和以2为底的指数n，即val = x * 2n
	math.frexp(10.0) => 0.625 4    0.625*2^4 = 10
*/
static int math_exp(lua_State *L) {
	lua_pushnumber(L, l_mathop(exp)(luaL_checknumber(L, 1)));
	return 1;
}
/*
	弧度转角度
		pi = 180
*/
static int math_deg(lua_State *L) {
	lua_pushnumber(L, luaL_checknumber(L, 1) * (l_mathop(180.0) / PI));
	return 1;
}
/*
	角度转弧度
*/
static int math_rad(lua_State *L) {
	lua_pushnumber(L, luaL_checknumber(L, 1) * (PI / l_mathop(180.0)));
	return 1;
}


/*
  取得一连串参数中最小的值
  首先获取lua栈的高度，然后用一个for循环得出最小值
  lua_compare判断第二个参数是否比第三个参数小，是的话，返回true（其实lua_compare的作用是看第四个参数LUA_OPLT，这里代表按照小于比较）
*/
static int math_min(lua_State *L) {
	int n = lua_gettop(L);  /* number of arguments 获取lua栈的高度*/
	int imin = 1;  /* index of current minimum value */
	int i;
	luaL_argcheck(L, n >= 1, 1, "value expected");
	for (i = 2; i <= n; i++) {
		if (lua_compare(L, i, imin, LUA_OPLT))
			imin = i;
	}
	lua_pushvalue(L, imin);
	return 1;
}

/*
	取得一连串参数中最大的值 参考上面
*/
static int math_max(lua_State *L) {
	int n = lua_gettop(L);  /* number of arguments */
	int imax = 1;  /* index of current maximum value */
	int i;
	luaL_argcheck(L, n >= 1, 1, "value expected");
	for (i = 2; i <= n; i++) {
		if (lua_compare(L, imax, i, LUA_OPLT))
			imax = i;
	}
	lua_pushvalue(L, imax);
	return 1;
}

/*
** This function uses 'double' (instead of 'lua_Number') to ensure that
** all bits from 'l_rand' can be represented, and that 'RANDMAX + 1.0'
** will keep full precision (ensuring that 'r' is always less than 1.0.)
*/

/*
  math_random是获取随机数的
  首先调用C函数获取一个[0,1)之间的随机数，然后就开始判断用户输入的参数个数来进行后续处理。
  如果用户没有输入参数，就默认返回[0,1)之间的随机数
  如果用户只输入一个参数，就代表要[1,x)之间的随机数，把low和up赋值等待后续处理
  如果用户输入两个参数，代表想要[x,y)之间的随机数，处理low和up
  最后通过最开始获取到的[0,1)之间的随机数，和low，up通过一些数学计算（r *= (double)(up - low) + 1.0）就获取到了最终的随机数
*/
static int math_random(lua_State *L) {
	lua_Integer low, up;
	double r = (double)l_rand() * (1.0 / ((double)L_RANDMAX + 1.0));
	switch (lua_gettop(L)) {  /* check number of arguments */
	case 0: {  /* no arguments */
		lua_pushnumber(L, (lua_Number)r);  /* Number between 0 and 1 */
		return 1;
	}
	case 1: {  /* only upper limit */
		low = 1;
		up = luaL_checkinteger(L, 1);
		break;
	}
	case 2: {  /* lower and upper limits */
		low = luaL_checkinteger(L, 1);
		up = luaL_checkinteger(L, 2);
		break;
	}
	default: return luaL_error(L, "wrong number of arguments");
	}
	/* random integer in the interval [low, up] */
	luaL_argcheck(L, low <= up, 1, "interval is empty");
	luaL_argcheck(L, low >= 0 || up <= LUA_MAXINTEGER + low, 1,
		"interval too large");
	r *= (double)(up - low) + 1.0;
	lua_pushinteger(L, (lua_Integer)r + low);
	return 1;
}


/*
  设置随机数种子
  调用C函数srand()
  它后面又调用了rand()是出于srand()执行失败的情况吧（我这么猜的）
*/
static int math_randomseed(lua_State *L) {
	l_srand((unsigned int)(lua_Integer)luaL_checknumber(L, 1));
	(void)l_rand(); /* discard first value to avoid undesirable correlations */
	return 0;
}


static int math_type(lua_State *L) {
	if (lua_type(L, 1) == LUA_TNUMBER) {
		if (lua_isinteger(L, 1))
			lua_pushliteral(L, "integer");
		else
			lua_pushliteral(L, "float");
	}
	else {
		luaL_checkany(L, 1);
		lua_pushnil(L);
	}
	return 1;
}


/*
** {==================================================================
** Deprecated functions (for compatibility only)
** ===================================================================
*/
#if defined(LUA_COMPAT_MATHLIB)

static int math_cosh(lua_State *L) {
	lua_pushnumber(L, l_mathop(cosh)(luaL_checknumber(L, 1)));
	return 1;
}

static int math_sinh(lua_State *L) {
	lua_pushnumber(L, l_mathop(sinh)(luaL_checknumber(L, 1)));
	return 1;
}

static int math_tanh(lua_State *L) {
	lua_pushnumber(L, l_mathop(tanh)(luaL_checknumber(L, 1)));
	return 1;
}

static int math_pow(lua_State *L) {
	lua_Number x = luaL_checknumber(L, 1);
	lua_Number y = luaL_checknumber(L, 2);
	lua_pushnumber(L, l_mathop(pow)(x, y));
	return 1;
}

static int math_frexp(lua_State *L) {
	int e;
	lua_pushnumber(L, l_mathop(frexp)(luaL_checknumber(L, 1), &e));
	lua_pushinteger(L, e);
	return 2;
}

static int math_ldexp(lua_State *L) {
	lua_Number x = luaL_checknumber(L, 1);
	int ep = (int)luaL_checkinteger(L, 2);
	lua_pushnumber(L, l_mathop(ldexp)(x, ep));
	return 1;
}

static int math_log10(lua_State *L) {
	lua_pushnumber(L, l_mathop(log10)(luaL_checknumber(L, 1)));
	return 1;
}

#endif
/* }================================================================== */


/*
	这些把上面写过的函数注册进mathlib结构里数组里面，这个结构体构造如下：
	typedef struct luaL_Reg {
	const char *name;
	lua_CFunction func;
	} luaL_Reg;
	name是函数的名字
	func是函数本身
	下面是lua_CFunction的定义，可以看得出来是一个返回值为int，参数为lua_State的函数指针
	typedef int(*lua_CFunction) (lua_State *L);
*/
static const luaL_Reg mathlib[] = {
  {"abs",   math_abs},
  {"acos",  math_acos},
  {"asin",  math_asin},
  {"atan",  math_atan},
  {"ceil",  math_ceil},
  {"cos",   math_cos},
  {"deg",   math_deg},
  {"exp",   math_exp},
  {"tointeger", math_toint},
  {"floor", math_floor},
  {"fmod",   math_fmod},
  {"ult",   math_ult},
  {"log",   math_log},
  {"max",   math_max},
  {"min",   math_min},
  {"modf",   math_modf},
  {"rad",   math_rad},
  {"random",     math_random},
  {"randomseed", math_randomseed},
  {"sin",   math_sin},
  {"sqrt",  math_sqrt},
  {"tan",   math_tan},
  {"type", math_type},
#if defined(LUA_COMPAT_MATHLIB)
  {"atan2", math_atan},
  {"cosh",   math_cosh},
  {"sinh",   math_sinh},
  {"tanh",   math_tanh},
  {"pow",   math_pow},
  {"frexp", math_frexp},
  {"ldexp", math_ldexp},
  {"log10", math_log10},
#endif
  /* placeholders */
  {"pi", NULL},
  {"huge", NULL},
  {"maxinteger", NULL},
  {"mininteger", NULL},
  {NULL, NULL}
};


/*
** Open math library
*/
/*
  最后通过luaopen_math把mathlib注册进lua里面，LUAMOD_API代表外部库的api函数标识
  并且把上面的一些macro也注册进了lua环境中
*/
LUAMOD_API int luaopen_math(lua_State *L) {
	luaL_newlib(L, mathlib);
	lua_pushnumber(L, PI);
	lua_setfield(L, -2, "pi");
	lua_pushnumber(L, (lua_Number)HUGE_VAL);
	lua_setfield(L, -2, "huge");
	lua_pushinteger(L, LUA_MAXINTEGER);
	lua_setfield(L, -2, "maxinteger");
	lua_pushinteger(L, LUA_MININTEGER);
	lua_setfield(L, -2, "mininteger");
	return 1;
}

