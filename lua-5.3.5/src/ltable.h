/*
** $Id: ltable.h,v 2.23.1.2 2018/05/24 19:39:05 roberto Exp $
** Lua tables (hash)
** See Copyright Notice in lua.h
*/

#ifndef ltable_h
#define ltable_h

#include "lobject.h"

// 此处的t就是table的实体对象
// gnode用来返回t的哈希部分的第i个节点，此处的i就是哈希部分0-size-1的整数值
#define gnode(t,i)	(&(t)->node[i])
// 此处的n是table的哈希部分的一个节点
// gval用来返回节点中的值（是一个TValue类型）
#define gval(n)		(&(n)->i_val)
// gnext用来返回此节点的下一个节点的地址（其实是一个偏移）
#define gnext(n)	((n)->i_key.nk.next)


/* 'const' to avoid wrong writings that can mess up field 'next' */
// 返回n的键里面的tvk的指针 const 返回的不能修改
#define gkey(n)		cast(const TValue*, (&(n)->i_key.tvk))

/*
** writable version of 'gkey'; allows updates to individual fields,
** but not to the whole (which has incompatible type)
*/
// wgkey是对gkey的可写版本，允许对单个字段进行更新
// 但不能整体更新
#define wgkey(n)		(&(n)->i_key.nk)
//清空table的元表
#define invalidateTMcache(t)	((t)->flags = 0)


/* true when 't' is using 'dummynode' as its hash part */
// 如果lastfree为NULL，说明这个table没有哈希部分（其实哈希部分的size为0，里面只有一个虚拟节点，定义在ltable.c中）
#define isdummy(t)		((t)->lastfree == NULL)


/* allocated size for hash nodes */
// 返回散列表的hash部分的大小 2^t.lsizenode <==> 1<<t.lsizenode;
#define allocsizenode(t)	(isdummy(t) ? 0 : sizenode(t))


/* returns the key, given the value of a table entry */
#define keyfromval(v) \
  (gkey(cast(Node *, cast(char *, (v)) - offsetof(Node, i_val)))) //offsetof(Node, i_val) i_val在node中的偏移值

// 返回key对应的i字段
LUAI_FUNC const TValue *luaH_getint (Table *t, lua_Integer key);
// 把t中key的value设置为传进来的value
LUAI_FUNC void luaH_setint (lua_State *L, Table *t, lua_Integer key,
                                                    TValue *value);
// 返回key对应的tsv字段
LUAI_FUNC const TValue *luaH_getshortstr (Table *t, TString *key);
LUAI_FUNC const TValue *luaH_getstr (Table *t, TString *key);
// 获取key对应的具体的值
LUAI_FUNC const TValue *luaH_get (Table *t, const TValue *key);
// 在t中插入一个新的key，可能会重新哈希
LUAI_FUNC TValue *luaH_newkey (lua_State *L, Table *t, const TValue *key);
// 如果传进来的key已经存在于t中，那么直接返回key对应的索引，不然就新建一个key
LUAI_FUNC TValue *luaH_set (lua_State *L, Table *t, const TValue *key);
// 在L里创建一张空表
LUAI_FUNC Table *luaH_new (lua_State *L);
// 重新设置t的数组部分和哈希部分的size并且做初始化
LUAI_FUNC void luaH_resize (lua_State *L, Table *t, unsigned int nasize,
                                                    unsigned int nhsize);
// 重新调整数组部分大
LUAI_FUNC void luaH_resizearray (lua_State *L, Table *t, unsigned int nasize);
// 释放table的内存
LUAI_FUNC void luaH_free (lua_State *L, Table *t);
// 实现table的递归。通过上一个键，来找到下一个键值对
LUAI_FUNC int luaH_next (lua_State *L, Table *t, StkId key);
// 获取有效t的长度（废弃）
LUAI_FUNC lua_Unsigned luaH_getn (Table *t);


#if defined(LUA_DEBUG)
// 返回key对应的mp位置
LUAI_FUNC Node *luaH_mainposition (const Table *t, const TValue *key);
// 判断t中的哈希部分是否存在
LUAI_FUNC int luaH_isdummy (const Table *t);
#endif


#endif
