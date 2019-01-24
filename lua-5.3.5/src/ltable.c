/*
** $Id: ltable.c,v 2.118.1.4 2018/06/08 16:22:51 roberto Exp $
** Lua tables (hash)
** See Copyright Notice in lua.h
*/

#define ltable_c
#define LUA_CORE

#include "lprefix.h"


/*
** Implementation of tables (aka arrays, objects, or hash tables).
** Tables keep its elements in two parts: an array part and a hash part.
** Non-negative integer keys are all candidates to be kept in the array
** part. The actual size of the array is the largest 'n' such that
** more than half the slots between 1 and n are in use.
** Hash uses a mix of chained scatter table with Brent's variation.   --Brent's variation 布伦特变量
** A main invariant of these tables is that, if an element is not
** in its main position (i.e. the 'original' position that its hash gives
** to it), then the colliding element is in its own main position.
** Hence even when the load factor reaches 100%, performance remains good.
*/

#include <math.h>
#include <limits.h>

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lgc.h"
#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "lvm.h"


/*
** Maximum size of array part (MAXASIZE) is 2^MAXABITS. MAXABITS is
** the largest integer such that MAXASIZE fits in an unsigned int.
*/
#define MAXABITS	cast_int(sizeof(int) * CHAR_BIT - 1)
#define MAXASIZE	(1u << MAXABITS)

/*
** Maximum size of hash part is 2^MAXHBITS. MAXHBITS is the largest
** integer such that 2^MAXHBITS fits in a signed int. (Note that the
** maximum number of elements in a table, 2^MAXABITS + 2^MAXHBITS, still
** fits comfortably in an unsigned int.)
*/
#define MAXHBITS	(MAXABITS - 1)

// #define gnode(t,i)  (&(t)->node[i])
// gnode的定义如上，用来返回t的哈希部分的第i个节点，此处的i就是哈希部分0-size-1的整数值
// 这里的sizenode(t)是返回t的哈希部分的尺寸
// 然后再调用lmod求出node所在位置的i值（lmod函数是最重要的）
// 再调用gnode来取得node节点
#define hashpow2(t,n)		(gnode(t, lmod((n), sizenode(t))))

#define hashstr(t,str)		hashpow2(t, (str)->hash)
#define hashboolean(t,p)	hashpow2(t, p)
#define hashint(t,i)		hashpow2(t, i)


/*
** for some types, it is better to avoid modulus by power of 2, as
** they tend to have many 2 factors.
*/
#define hashmod(t,n)	(gnode(t, ((n) % ((sizenode(t)-1)|1))))


#define hashpointer(t,p)	hashmod(t, point2uint(p))

/*用于空node节点部分的元素*/
#define dummynode		(&dummynode_)

static const Node dummynode_ = {
  {NILCONSTANT},  /* value */
  {{NILCONSTANT, 0}}  /* key */
};


/*
** Hash for floating-point numbers.
** The main computation should be just
**     n = frexp(n, &i); return (n * INT_MAX) + i
** but there are some numerical subtleties.
** In a two-complement representation, INT_MAX does not has an exact
** representation as a float, but INT_MIN does; because the absolute
** value of 'frexp' is smaller than 1 (unless 'n' is inf/NaN), the
** absolute value of the product 'frexp * -INT_MIN' is smaller or equal
** to INT_MAX. Next, the use of 'unsigned int' avoids overflows when
** adding 'i'; the use of '~u' (instead of '-u') avoids problems with
** INT_MIN.
*/
#if !defined(l_hashfloat)
static int l_hashfloat(lua_Number n) {
	int i;
	lua_Integer ni;
	n = l_mathop(frexp)(n, &i) * -cast_num(INT_MIN);
	if (!lua_numbertointeger(n, &ni)) {  /* is 'n' inf/-inf/NaN? */
		lua_assert(luai_numisnan(n) || l_mathop(fabs)(n) == cast_num(HUGE_VAL));
		return 0;
	}
	else {  /* normal case */
		unsigned int u = cast(unsigned int, i) + cast(unsigned int, ni);
		return cast_int(u <= cast(unsigned int, INT_MAX) ? u : ~u);
	}
}
#endif


/*
** returns the 'main' position of an element in a table (that is, the index
** of its hash value)
*/
/*计算key的hash的mainposition，可以的类型如下几种*/
static Node *mainposition(const Table *t, const TValue *key) {
	switch (ttype(key)) {
	case LUA_TNUMINT:
		return hashint(t, ivalue(key));
	case LUA_TNUMFLT:
		return hashmod(t, l_hashfloat(fltvalue(key)));
	case LUA_TSHRSTR:
		return hashstr(t, tsvalue(key));
	case LUA_TLNGSTR:
		return hashpow2(t, luaS_hashlongstr(tsvalue(key)));
	case LUA_TBOOLEAN:
		return hashboolean(t, bvalue(key));
	case LUA_TLIGHTUSERDATA:
		return hashpointer(t, pvalue(key));
	case LUA_TLCF:
		return hashpointer(t, fvalue(key));
	default:
		lua_assert(!ttisdeadkey(key));
		return hashpointer(t, gcvalue(key));
	}
}


/*
** returns the index for 'key' if 'key' is an appropriate key to live in
** the array part of the table, 0 otherwise.
*/
static unsigned int arrayindex(const TValue *key) {
	if (ttisinteger(key)) {
		lua_Integer k = ivalue(key);
		if (0 < k && (lua_Unsigned)k <= MAXASIZE)
			return cast(unsigned int, k);  /* 'key' is an appropriate array index 合适的数组索引*/
	}
	return 0;  /* 'key' did not match some condition */
}


/*
** returns the index of a 'key' for table traversals. First goes all
** elements in the array part, then elements in the hash part. The
** beginning of a traversal is signaled by 0.
*/
// 找到key在Table中的索引，先判断是否在数组中，不再的话在hash部分查找
// 如果是在哈希部分的话，就先找出和这个key对应的mp
// luaV_rawequalobj比较两个obj是否内存意义上相等，或者看这个key是不是已经被回收了
// 满足任何一个都可以得到key对应的i，这个i是key在hash上的索引
// 然后返回(i + 1) + t->sizearray
// 如果luaV_rawequalobj返回false的话，就说明这个key在mp的链表上，然后遍历链表继续查找
static unsigned int findindex(lua_State *L, Table *t, StkId key) {
	unsigned int i;
	if (ttisnil(key)) return 0;  /* first iteration */
	i = arrayindex(key);
	if (i != 0 && i <= t->sizearray)  /* is 'key' inside array part? */
		return i;  /* yes; that's the index */
	else {
		int nx;
		Node *n = mainposition(t, key);
		for (;;) {  /* check whether 'key' is somewhere in the chain */
		  /* key may be dead already, but it is ok to use it in 'next' */
			if (luaV_rawequalobj(gkey(n), key) ||
				(ttisdeadkey(gkey(n)) && iscollectable(key) &&
					deadvalue(gkey(n)) == gcvalue(key))) {
				i = cast_int(n - gnode(t, 0));  /* key index in hash table */
				/* hash elements are numbered after array ones */
				return (i + 1) + t->sizearray;
			}
			nx = gnext(n);
			if (nx == 0)
				luaG_runerror(L, "invalid key to 'next'");  /* key not found */
			else n += nx;
		}
	}
}

//1) 如果位于数组部分，则由搜索位置开始向后索引数组部分的值，查找到一个非 nil 的值则向 lua 栈中压入当前位置的键值对。
//2) 如果位于哈希表部分，那么也是类似的，直接按照哈希表的节点顺序遍历每个哈希节点，直到找到一个非 nil 的节点。
int luaH_next(lua_State *L, Table *t, StkId key) {
	unsigned int i = findindex(L, t, key);  /* find original element */
	for (; i < t->sizearray; i++) {  /* try first array part */
		if (!ttisnil(&t->array[i])) {  /* a non-nil value? */
			setivalue(key, i + 1);
			setobj2s(L, key + 1, &t->array[i]);
			return 1;
		}
	}
	for (i -= t->sizearray; cast_int(i) < sizenode(t); i++) {  /* hash part */
		if (!ttisnil(gval(gnode(t, i)))) {  /* a non-nil value? */
			setobj2s(L, key, gkey(gnode(t, i)));
			setobj2s(L, key + 1, gval(gnode(t, i)));
			return 1;
		}
	}
	return 0;  /* no more elements */
}


/*
** {=============================================================
** Rehash
**	无论是array还是hash表，都是以2的倍数进行扩展的。比较有区别的是，
**	array数组sizearray记录的是真实大小，而hash表的lsizenode记录的是2的倍数。
**	当hash表空间满的时候，才会重新分配array和hash表。
**	比较重要的两个函数是rehash和resize，前一个是重新算出要分配的空间，后一个是创建空间。先分析下rehash函数：
** ==============================================================
*/

/*
** Compute the optimal size for the array part of table 't'. 'nums' is a
** "count array" where 'nums[i]' is the number of integers in the table
** between 2^(i - 1) + 1 and 2^i. 'pna' enters with the total number of
** integer keys in the table and leaves with the number of keys that
** will go to the array part; return the optimal size.
*/
// 计算t中最理想的数组大小。nums数组中第i个元素存放的是table中key在2的i-1次幂和2的i次幂之间的元素数量。
// pna是table中正整数的数量
// 遍历这个nums数组，获得其范围区间内所包含的整数数量大于50%的最大索引，作为重新哈希之后的数组大小，超过这个范围的正整数，就分配到哈希部分了
// computesizes 通过已知所有的（包括即将插入的）正整数键值在(2 ^ (i - 1), 2 ^ i] 的分布，和正整数键数量的总数，
// 来计算出一个新的数组部分的大小。在数组范围外的正整数键放到哈希表中：
static unsigned int computesizes(unsigned int nums[], unsigned int *pna) {
	int i;
	unsigned int twotoi;  /* 2^i (candidate for optimal size) */
	unsigned int a = 0;  /* number of elements smaller than 2^i */
	unsigned int na = 0;  /* number of elements to go to array part */
	unsigned int optimal = 0;  /* optimal size for array part */
	/* loop while keys can fill more than half of total size */
	for (i = 0, twotoi = 1;
		twotoi > 0 && *pna > twotoi / 2;
		i++, twotoi *= 2) {
		if (nums[i] > 0) {
			a += nums[i];
			if (a > twotoi / 2) {  /* more than half elements present? */
				optimal = twotoi;  /* optimal size (till now) */
				na = a;  /* all elements up to 'optimal' will go to array part */
			}
		}
	}
	lua_assert((optimal == 0 || optimal / 2 < na) && na <= optimal);
	*pna = na;
	return optimal;
}

// arrayindex返回key的索引，返回的值不等于0才算key在t的数组部分
// luaO_ceillog2也就是求出k的以2为底的对数，在对结果进行向上取整
// 总的来说，countint的作用就是对nums的某些位置进行计算
// 如果即将插入的新键是一个正整数，那么也把它记录到 nums 数组里，同时否则什么也不做。
static int countint(const TValue *key, unsigned int *nums) {
	unsigned int k = arrayindex(key);
	if (k != 0) {  /* is 'key' an appropriate array index? */
		nums[luaO_ceillog2(k)]++;  /* count as such */
		return 1;
	}
	else
		return 0;
}


/*
** Count keys in array part of table 't': Fill 'nums[i]' with
** number of keys that will go into corresponding slice and return
** total number of non-nil keys.
*/
// numusearray函数遍历表中的数组部分，计算其中的元素数量，并更新对应的nums数组中的元素数量
// 里面的操作基本大意是，找出数组部分的2^(lg - 1), 2^lg之间的元素数量，然后对nums的对应格子进行赋值
// 然后记录下来array的数量并且返回

// numusearray 遍历了整个数组部分，以区间(2 ^ (i - 1), 2 ^ i] 为步长来遍历每个区间的非空的值，
// 记录数量到数组 nums 中，同时最终返回数组中非空值的总数：
static unsigned int numusearray(const Table *t, unsigned int *nums) {
	int lg;
	unsigned int ttlg;  /* 2^lg */
	unsigned int ause = 0;  /* summation of 'nums' */
	unsigned int i = 1;  /* count to traverse all array keys */
	/* traverse each slice */
	for (lg = 0, ttlg = 1; lg <= MAXABITS; lg++, ttlg *= 2) {
		unsigned int lc = 0;  /* counter */
		unsigned int lim = ttlg;
		if (lim > t->sizearray) {
			lim = t->sizearray;  /* adjust upper limit */
			if (i > lim)
				break;  /* no more elements to count */
		}
		/* count elements in range (2^(lg - 1), 2^lg] */
		for (; i <= lim; i++) {
			if (!ttisnil(&t->array[i - 1]))
				lc++;
		}
		nums[lg] += lc;
		ause += lc;
	}
	return ause;
}

// 计算t中哈希部分的元素数量
// 因为其中也可能存放了正整数，需要根据这里的正整数数量更新对应的nums数组元素数量
// numusehash 遍历了整个哈希表部分来进行计数哈希表部分的使用总数。
// 它也同时统计了哈希部分所有正整数键的数量累加至 na，因为这些键可能会在 rehash 后放入数组部分
static int numusehash(const Table *t, unsigned int *nums, unsigned int *pna) {
	int totaluse = 0;  /* total number of elements */
	int ause = 0;  /* elements added to 'nums' (can go to array part) */
	int i = sizenode(t);
	while (i--) {
		Node *n = &t->node[i];
		if (!ttisnil(gval(n))) {
			ause += countint(gkey(n), nums);
			totaluse++;
		}
	}
	*pna += ause;
	return totaluse;
}

// 如果数组部分需要的长度大于原有的长度: 则通过 setarrayvector 分配新的数组长度 1，并且把新增的部分赋值为 nil。
// 如果旧的数组含有数据，分配函数 luaM_reallocvector 会复制这部分数据到新数组中。
static void setarrayvector(lua_State *L, Table *t, unsigned int size) {
	unsigned int i;
	luaM_reallocvector(L, t->array, t->sizearray, size, TValue);
	for (i = t->sizearray; i < size; i++)
		setnilvalue(&t->array[i]);
	t->sizearray = size;
}

// 对表的哈希部分大小进行设置
// 如果传进来的size为0，那么t的node(指向散列表起始位置的指针)是指一个虚拟节点
// lsizenode是该表中以2为底的散列表大小的对数值，此处设置为0
// lastfree指向散列表最后位置的指针，此处设置为NULL

// 如果size不为0，那么就根据传入的size来计算哈希部分的lsizenode值（luaO_ceillog2是计算出size的以2为底的对数）
// 如果size大于MAXHBITS则报错。MAXHBITS是允许哈希部分最大的2的幂
// 然后twoto的意思为求出lsize的2^lsize的结果  定义为#define twoto(x)  (1<<(x))
// 设置完size之后 下面就开始申请哈希部分的空间了，让node指向新空间的起始地址
// 然后在循环里面对size个元素进行设置
// gnode用来返回t的哈希部分的第i个节点
// gnext用来返回此节点的下一个节点的地址（其实是一个偏移）
// #define wgkey(n)    (&(n)->i_key.nk)
// #define gval(n)   (&(n)->i_val)
// setnilvalue(wgkey(n)); 让n的i_key.nk字段设为NULL
// setnilvalue(gval(n));  让n的i_val字段设为NULL
// 然后再对t的lsizenode和lastfree设置就完成了哈希部分的初始化
// 此处lastfree指向的是size节点，也就是哈希部分的下一个节点
static void setnodevector(lua_State *L, Table *t, unsigned int size) {
	if (size == 0) {  /* no elements to hash part? */
		t->node = cast(Node *, dummynode);  /* use common 'dummynode' */
		t->lsizenode = 0;
		t->lastfree = NULL;  /* signal that it is using dummy node */
	}
	else {
		int i;
		int lsize = luaO_ceillog2(size);
		if (lsize > MAXHBITS)
			luaG_runerror(L, "table overflow");
		size = twoto(lsize);
		t->node = luaM_newvector(L, size, Node);
		for (i = 0; i < (int)size; i++) {
			Node *n = gnode(t, i);
			gnext(n) = 0;
			setnilvalue(wgkey(n));
			setnilvalue(gval(n));
		}
		t->lsizenode = cast_byte(lsize);
		t->lastfree = gnode(t, size);  /* all positions are free */ //t->lastfree 指向最后一个节点的后一个位置
	}
}


typedef struct {
	Table *t;
	unsigned int nhsize;
} AuxsetnodeT;


static void auxsetnode(lua_State *L, void *ud) {
	AuxsetnodeT *asn = cast(AuxsetnodeT *, ud);
	setnodevector(L, asn->t, asn->nhsize);
}

/*
	重新分配数组部分和hash部分的空间
	nasize 数组部分的最佳大小
*/
void luaH_resize(lua_State *L, Table *t, unsigned int nasize,
	unsigned int nhsize) {
	unsigned int i;
	int j;
	AuxsetnodeT asn;
	unsigned int oldasize = t->sizearray;
	int oldhsize = allocsizenode(t);
	Node *nold = t->node;  /* save old hash ... */
	if (nasize > oldasize)  /* array part must grow? 扩张数组部分*/
		setarrayvector(L, t, nasize);
	/* create new hash part with appropriate size */
	asn.t = t; asn.nhsize = nhsize;
	if (luaD_rawrunprotected(L, auxsetnode, &asn) != LUA_OK) {  /* mem. error? */
		setarrayvector(L, t, oldasize);  /* array back to its original size */
		luaD_throw(L, LUA_ERRMEM);  /* rethrow memory error */
	}
	if (nasize < oldasize) {  /* array part must shrink? */
		t->sizearray = nasize;
		/* re-insert elements from vanishing slice */
		for (i = nasize; i < oldasize; i++) {
			if (!ttisnil(&t->array[i]))
				luaH_setint(L, t, i + 1, &t->array[i]);
		}
		/* shrink array 收缩数组*/
		luaM_reallocvector(L, t->array, oldasize, nasize, TValue);
	}
	/* re-insert elements from hash part */
	for (j = oldhsize - 1; j >= 0; j--) {
		Node *old = nold + j;
		if (!ttisnil(gval(old))) {
			/* doesn't need barrier/invalidate cache, as entry was
			   already present in the table */
			setobjt2t(L, luaH_set(L, t, gkey(old)), gval(old));
		}
	}
	//释放老hash表空间
	if (oldhsize > 0)  /* not the dummy node? */
		luaM_freearray(L, nold, cast(size_t, oldhsize)); /* free old hash */
}


void luaH_resizearray(lua_State *L, Table *t, unsigned int nasize) {
	int nsize = allocsizenode(t);
	luaH_resize(L, t, nasize, nsize);
}

/*
** nums[i] = number of keys 'k' where 2^(i - 1) < k <= 2^i
*/
/**
	添加key，并且重新hash，主要计算数组与hash部分的大小，最终在luaH_resize中重新分配大小
*/
static void rehash(lua_State *L, Table *t, const TValue *ek) {
	unsigned int asize;  /* optimal size for array part 数组部分的最优大小*/
	unsigned int na;  /* number of keys in the array part 数组部分所有key的个数，也就是数组部分使用的总数*/
	unsigned int nums[MAXABITS + 1]; /*累计各个区间整数key不为nil的个数，包括hash, 例如nums[i]表示累计在[2 ^ (i - 1)，2^i]区间内的整数key个数 */
	int i;
	int totaluse;//记录所有已存在的键，包括hash和array，即table里的成员个数
	for (i = 0; i <= MAXABITS; i++) nums[i] = 0;  /* reset counts */
	na = numusearray(t, nums);  /* count keys in array part */
	totaluse = na;  /* all those keys are integer keys */
	totaluse += numusehash(t, nums, &na);  /* count keys in hash part 统计hash表里已有的键，以及整数键的个数已经区间分布*/
	/* count extra key 计算key*/
	na += countint(ek, nums);
	totaluse++;
	/* compute new size for array part */
	asize = computesizes(nums, &na);
	/* resize the table to new computed sizes */
	luaH_resize(L, t, asize, totaluse - na);
}



/*
** }=============================================================
*/

/*
	创建表
*/
Table *luaH_new(lua_State *L) {
	GCObject *o = luaC_newobj(L, LUA_TTABLE, sizeof(Table));
	Table *t = gco2t(o);
	t->metatable = NULL;
	t->flags = cast_byte(~0);
	t->array = NULL;
	t->sizearray = 0;
	setnodevector(L, t, 0);
	return t;
}

/*释放表
	显示放hash部分
	再释放数组部分
*/
void luaH_free(lua_State *L, Table *t) {
	if (!isdummy(t))
		luaM_freearray(L, t->node, cast(size_t, sizenode(t)));
	luaM_freearray(L, t->array, t->sizearray);
	luaM_free(L, t);
}

/**
	当查找的 mp 由于冲突被其它键所占用时，会通过 getfreepos 尝试获取一个可用的节点来存储新的键。
	lastfree 初始指向哈希表的最后一个节点的下一个位置，向前迭代直到找到一个空节点，如果迭代到哈希表头则表明无可用节点，返回 NULL。
*/
static Node *getfreepos(Table *t) {
	if (!isdummy(t)) {
		while (t->lastfree > t->node) {
			t->lastfree--;
			if (ttisnil(gkey(t->lastfree)))
				return t->lastfree;
		}
	}
	return NULL;  /* could not find a free place */
}



/*
** inserts a new key into a hash table; first, check whether key's main
** position is free. If not, check whether colliding node is in its main
** position or not: if it is not, move colliding node to an empty place and
** put new key in its main position; otherwise (colliding node is in its main
** position), new key goes to an empty position.
*/
// 在插入一个新的key的时候首先判断key是不是NULL，是的话就报错
// 然后接着判断，如果是数字，若是未定义数字也错误返回
// luaV_tointeger看一下 key的索引是否可以转换为int，此处0的意思就是不接受取整，只能是int
// 然后用构造出来的aux对key初始化，这样就算是处理完了key，在拿着key来取得最重要的mainposition
// 然后调用mainposition求出t中key对应的mainposition，返回值是一个Node *类型

// 如果t的哈希部分为NULL或者mp节点不为NULL都会走if的逻辑
// 首先就是定义一个othern的节点和一个f节点
// getfreepos获取一个可以用的空闲节点,如果返回NULL则说明哈希部分满员了 需要重新哈希
// 当返回一个可用的节点时，会判断:
// 1.如果属于同一主位置节点链下 (现有的 mp 位置的键的主位置节点和新插入的 key 的主位置节点确实指向的同一个节点)，
// 那么把空节点插入到主位置节点之后（每个节点的 TKey 结构中存储着指向下一个节点的偏移值）。走else逻辑.这个地方有点绕,好好理解
// 2) 如果不属于同一主位置节点链下，则意味着原本通过 mainposition(newkey) 直接定位的节点被其它节点链中的某个节点占用,走if逻辑
// 这里的othern保存的就是得到的mp上的node里面的key对应的mp值
// if逻辑：
// 如果得到的mp被其他节点链中的节点占用时，则由othern开始开始向后遍历一直到mp的前一个位置，然后将mp的数据移动到空节点上，othern指向新的节点，旧的节点用来放入新插入的键
// gnext(othern) = cast_int(f - othern);  让othern指向f节点
// else逻辑：
// 将f节点插入mp节点之后
// 然后就设置一下mp的k，并且返回mp的val，让用户操
TValue *luaH_newkey(lua_State *L, Table *t, const TValue *key) {
	Node *mp;
	TValue aux;
	if (ttisnil(key)) luaG_runerror(L, "table index is nil");
	else if (ttisfloat(key)) {
		lua_Integer k;
		if (luaV_tointeger(key, &k, 0)) {  /* does index fit in an integer? */
			setivalue(&aux, k);
			key = &aux;  /* insert it as an integer */
		}
		else if (luai_numisnan(fltvalue(key)))
			luaG_runerror(L, "table index is NaN");
	}
	mp = mainposition(t, key);
	if (!ttisnil(gval(mp)) || isdummy(t)) {  /* main position is taken? */
		Node *othern;
		Node *f = getfreepos(t);  /* get a free place */
		if (f == NULL) {  /* cannot find a free place? */
			rehash(L, t, key);  /* grow table */
			/* whatever called 'newkey' takes care of TM cache */
			return luaH_set(L, t, key);  /* insert key into grown table */
		}
		lua_assert(!isdummy(t));
		othern = mainposition(t, gkey(mp));
		//冲突节点如果不在该位置
		if (othern != mp) {  /* is colliding node out of its main position? */
		  /* yes; move colliding node into free position */
			while (othern + gnext(othern) != mp)  /* find previous *///找到mp的上一个节点
				othern += gnext(othern);
			gnext(othern) = cast_int(f - othern);  /* rechain to point to 'f' */
			*f = *mp;  /* copy colliding node into free pos. (mp->next also goes) */
			if (gnext(mp) != 0) {
				gnext(f) += cast_int(mp - f);  /* correct 'next' */
				gnext(mp) = 0;  /* now 'mp' is free */
			}
			setnilvalue(gval(mp));
		}
		else {  /* colliding node is in its own main position */  /*冲突节点如果在该位置*/
		  /* new node will go into free position */
			if (gnext(mp) != 0)
				gnext(f) = cast_int((mp + gnext(mp)) - f);  /* chain new position */
			else lua_assert(gnext(f) == 0);
			gnext(mp) = cast_int(f - mp);
			mp = f;
		}
	}
	setnodekey(L, &mp->i_key, key);
	luaC_barrierback(L, t, key);
	lua_assert(ttisnil(gval(mp)));
	return gval(mp);
}


/*
** search function for integers
*/
/*
	找到key对应的Value，现在数组部分查找，否则在hash部分找
*/
const TValue *luaH_getint(Table *t, lua_Integer key) {
	/* (1 <= key && key <= t->sizearray) */
	if (l_castS2U(key) - 1 < t->sizearray)
		return &t->array[key - 1];
	else {
		Node *n = hashint(t, key);
		for (;;) {  /* check whether 'key' is somewhere in the chain */
			if (ttisinteger(gkey(n)) && ivalue(gkey(n)) == key)
				return gval(n);  /* that's it */
			else {
				int nx = gnext(n);
				if (nx == 0) break;
				n += nx;
			}
		}
		return luaO_nilobject;
	}
}


/*
** search function for short strings
*/
/*
	在hash部分搜索key为shortstring对应的TVale
*/
const TValue *luaH_getshortstr(Table *t, TString *key) {
	Node *n = hashstr(t, key);
	lua_assert(key->tt == LUA_TSHRSTR);
	for (;;) {  /* check whether 'key' is somewhere in the chain */
		const TValue *k = gkey(n);
		if (ttisshrstring(k) && eqshrstr(tsvalue(k), key))
			return gval(n);  /* that's it */
		else {
			int nx = gnext(n);
			if (nx == 0)
				return luaO_nilobject;  /* not found */
			n += nx;
		}
	}
}


/*
** "Generic" get version. (Not that generic: not valid for integers,
** which may be in array part, nor for floats with integral values.)
*/
static const TValue *getgeneric(Table *t, const TValue *key) {
	Node *n = mainposition(t, key);
	for (;;) {  /* check whether 'key' is somewhere in the chain */
		if (luaV_rawequalobj(gkey(n), key))	
			return gval(n);  /* that's it */
		else {
			int nx = gnext(n);
			if (nx == 0)
				return luaO_nilobject;  /* not found */
			n += nx;
		}
	}
}


const TValue *luaH_getstr(Table *t, TString *key) {
	if (key->tt == LUA_TSHRSTR)
		return luaH_getshortstr(t, key);
	else {  /* for long strings, use generic case */
		TValue ko;
		setsvalue(cast(lua_State *, NULL), &ko, key);
		return getgeneric(t, &ko);
	}
}


/*
** main search function
*/
const TValue *luaH_get(Table *t, const TValue *key) {
	switch (ttype(key)) {
	case LUA_TSHRSTR: return luaH_getshortstr(t, tsvalue(key));
	case LUA_TNUMINT: return luaH_getint(t, ivalue(key));
	case LUA_TNIL: return luaO_nilobject;
	case LUA_TNUMFLT: {
		lua_Integer k;
		if (luaV_tointeger(key, &k, 0)) /* index is int? */
			return luaH_getint(t, k);  /* use specialized version */
		  /* else... */
	}  /* FALLTHROUGH */
	default:
		return getgeneric(t, key);
	}
}


/*
** beware: when using this function you probably need to check a GC
** barrier and invalidate the TM cache.
*/
/*
	设置key位置的Node节点的值，如果存在node则直接返回，否则创建一个key对应的node并且返回
	（返回后应该在外面操作赋值）
*/
TValue *luaH_set(lua_State *L, Table *t, const TValue *key) {
	const TValue *p = luaH_get(t, key);
	if (p != luaO_nilobject)
		return cast(TValue *, p);
	else return luaH_newkey(L, t, key);
}

/*
	设这key对应位置node节点设置为value的值
*/
void luaH_setint(lua_State *L, Table *t, lua_Integer key, TValue *value) {
	const TValue *p = luaH_getint(t, key);
	TValue *cell;
	if (p != luaO_nilobject)
		cell = cast(TValue *, p);
	else {
		TValue k;
		setivalue(&k, key);
		cell = luaH_newkey(L, t, &k);
	}
	setobj2t(L, cell, value);
}


static lua_Unsigned unbound_search(Table *t, lua_Unsigned j) {
	lua_Unsigned i = j;  /* i is zero or a present index */
	j++;
	/* find 'i' and 'j' such that i is present and j is not */
	while (!ttisnil(luaH_getint(t, j))) {
		i = j;
		if (j > l_castS2U(LUA_MAXINTEGER) / 2) {  /* overflow? */
		  /* table was built with bad purposes: resort to linear search */
			i = 1;
			while (!ttisnil(luaH_getint(t, i))) i++;
			return i - 1;
		}
		j *= 2;
	}
	/* now do a binary search between them */
	while (j - i > 1) {
		lua_Unsigned m = (i + j) / 2;
		if (ttisnil(luaH_getint(t, m))) j = m;
		else i = m;
	}
	return i;
}


/*
** Try to find a boundary in table 't'. A 'boundary' is an integer index
** such that t[i] is non-nil and t[i+1] is nil (and 0 if t[1] is nil).
*/
lua_Unsigned luaH_getn(Table *t) {
	unsigned int j = t->sizearray;
	if (j > 0 && ttisnil(&t->array[j - 1])) {
		/* there is a boundary in the array part: (binary) search for it */
		unsigned int i = 0;
		while (j - i > 1) {
			unsigned int m = (i + j) / 2;
			if (ttisnil(&t->array[m - 1])) j = m;
			else i = m;
		}
		return i;
	}
	/* else must find a boundary in hash part */
	else if (isdummy(t))  /* hash part is empty? */
		return j;  /* that is easy... */
	else return unbound_search(t, j);
}



#if defined(LUA_DEBUG)

Node *luaH_mainposition(const Table *t, const TValue *key) {
	return mainposition(t, key);
}

int luaH_isdummy(const Table *t) { return isdummy(t); }

#endif
