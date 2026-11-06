// Printed from the bend branch's bend/effs/ic.c by its bend/dev/genic.bend; do not
// edit by hand. The rule table there is proven to be bend/IC.bend's rules
// (bend/NetProof.bend, table_is_rules).
#define TEL_IC_STANDALONE 1

// IC, native
// ==========

// nt.reduce (bend/Native.bend): bend/IC.bend's loop (`reduce`) in C, on
// the same net. The agents are one Array<U32>, eight words per agent; the
// templates another; the rest of the control state (Ctl) comes in and goes
// out as words. Every rule here is IC.bend's, word for word: the same
// agents allocated in the same order from the same free list, the same
// wires, the same LIFO stack of active pairs. So the net this leaves is
// the net IC.bend's loop would leave, and so are the interactions spent.
//
// It fires every pair it can and stops at the first it leaves to Bend:
// the rules that make a stuck value (their message is a Bend String, kept
// in Ctl's cold part), an applied unbounded-recursion step (--fast counts
// its unrolls there too), and a pair no rule fires. Bend fires that pair
// with IC.bend's own code (Native.bend's loop), then calls this again.
// An internal error comes back as a code (`why`) that Bend turns into
// IC.bend's message.
//
// The parts between `// <generated NAME>` and `// </generated>` are printed
// by bend/dev/genic.bend: the dispatch from IC.bend's rule.of, the rules from
// bend/Rules.bend's table. Change them there. What is written here by hand is
// the machine under them: the net's words, instantiation, guided copying and
// the loop.
//
// With TEL_IC_STANDALONE defined this file has no Bend in it: the net is a
// malloc'd block, and the host (master's Telomare.IC.Native) fires what this
// leaves to Bend above. master's cbits/tel_ic.c is this file with that define.

#ifdef TEL_IC_STANDALONE
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef uint8_t  u8;
typedef uint32_t u32;
typedef uint64_t u64;
#endif

// <generated dispatch>
#define NT_ROOT 1
#define NT_EXT 2
#define NT_ERA 3
#define NT_ZERO 4
#define NT_GATE 5
#define NT_CONST 6
#define NT_REF 7
#define NT_PAIR 8
#define NT_ABORTED 9
#define NT_DUP 10
#define NT_SPLIT 11
#define NT_SETENV 12
#define NT_APPLY 13
#define NT_SCRUT 14
#define NT_LEFT 16
#define NT_RIGHT 17
#define NT_STUCK 18
#define NT_KINDS 19

// The rules, as IC.bend's type Rule names them. NT_BEND: left to Bend.
enum {
  NT_NONE,
  NT_BEND,
  NT_SETENV_PAIR,
  NT_PASS,
  NT_APPLY_REF,
  NT_AWAIT_GATE,
  NT_PASS_APP,
  NT_SELECT_GATE,
  NT_SCRUT_PAIR,
  NT_PROJECT_LEFT,
  NT_PROJECT_RIGHT,
  NT_SPLIT_PAIR,
  NT_SPLIT_ZERO,
  NT_SPLIT_ABORTED,
  NT_SPLIT_STUCK,
  NT_ERA_PAIR,
  NT_ERA_ABORTED,
  NT_ERA_LEAF,
  NT_DUP_PLANNED,
  NT_DUP_ABORTED,
  NT_DUP_DUP,
  NT_DUP_LEAF,
  NT_OPEN,
};

// IC.bend's rule.of, for the first kind then the second.
static const u8 nt_rule[NT_KINDS][NT_KINDS] = {
  [NT_ERA] = {[NT_ZERO] = NT_ERA_LEAF, [NT_GATE] = NT_ERA_LEAF, [NT_CONST] = NT_ERA_LEAF, [NT_REF] = NT_ERA_LEAF, [NT_PAIR] = NT_ERA_PAIR, [NT_ABORTED] = NT_ERA_ABORTED, [NT_STUCK] = NT_ERA_LEAF, },
  [NT_DUP] = {[NT_ZERO] = NT_DUP_LEAF, [NT_GATE] = NT_DUP_LEAF, [NT_CONST] = NT_DUP_LEAF, [NT_REF] = NT_DUP_LEAF, [NT_PAIR] = NT_DUP_PLANNED, [NT_ABORTED] = NT_DUP_ABORTED, [NT_DUP] = NT_DUP_DUP, [NT_STUCK] = NT_DUP_LEAF, },
  [NT_SPLIT] = {[NT_ZERO] = NT_SPLIT_ZERO, [NT_GATE] = NT_BEND, [NT_CONST] = NT_OPEN, [NT_REF] = NT_BEND, [NT_PAIR] = NT_SPLIT_PAIR, [NT_ABORTED] = NT_SPLIT_ABORTED, [NT_STUCK] = NT_SPLIT_STUCK, },
  [NT_SETENV] = {[NT_ZERO] = NT_BEND, [NT_GATE] = NT_BEND, [NT_CONST] = NT_OPEN, [NT_REF] = NT_BEND, [NT_PAIR] = NT_SETENV_PAIR, [NT_ABORTED] = NT_PASS, [NT_STUCK] = NT_PASS, },
  [NT_APPLY] = {[NT_ZERO] = NT_BEND, [NT_GATE] = NT_AWAIT_GATE, [NT_CONST] = NT_OPEN, [NT_REF] = NT_APPLY_REF, [NT_PAIR] = NT_BEND, [NT_ABORTED] = NT_PASS_APP, [NT_STUCK] = NT_PASS_APP, },
  [NT_SCRUT] = {[NT_ZERO] = NT_SELECT_GATE, [NT_GATE] = NT_BEND, [NT_CONST] = NT_OPEN, [NT_REF] = NT_BEND, [NT_PAIR] = NT_SCRUT_PAIR, [NT_ABORTED] = NT_PASS, [NT_STUCK] = NT_PASS, },
  [NT_LEFT] = {[NT_ZERO] = NT_PASS, [NT_GATE] = NT_BEND, [NT_CONST] = NT_OPEN, [NT_REF] = NT_BEND, [NT_PAIR] = NT_PROJECT_LEFT, [NT_ABORTED] = NT_PASS, [NT_STUCK] = NT_PASS, },
  [NT_RIGHT] = {[NT_ZERO] = NT_PASS, [NT_GATE] = NT_BEND, [NT_CONST] = NT_OPEN, [NT_REF] = NT_BEND, [NT_PAIR] = NT_PROJECT_RIGHT, [NT_ABORTED] = NT_PASS, [NT_STUCK] = NT_PASS, },
};
// </generated>

// Internal errors (IC.bend's `fail` messages), for Bend to name.
#define NT_WHY_PAIR   1  // "dupRegion: nothing to pair"
#define NT_WHY_COPIES 2  // "dup-closure: no copies"

typedef struct {
#ifndef TEL_IC_STANDALONE
  Env  e;
  Term mt;   // the agents' block
#endif
  u32* m;    // its words
  u32* t;    // the templates' words
  u32  sp, bump, free, label, fuel, err, cap, why;
  u32* js;   // guided copying's jobs (dupRegion), a stack of (s, p)
  u32  jn, jcap;
  u32* vs;   // and its copies
  u32  vn, vcap;
} Nt;

// The net
// -------

#define NT_K(x, n)  ((x)->m[(n) * 8])
#define NT_A(x, n)  ((x)->m[(n) * 8 + 4])
#define NT_B(x, n)  ((x)->m[(n) * 8 + 5])
#define NT_P1(x, n) ((x)->m[(n) * 8 + 2])
#define NT_P2(x, n) ((x)->m[(n) * 8 + 3])
#define NT_IDX(p)   (((p) >> 2) * 8 + 1 + ((p) & 3))

// grow: twice the room for agents and stacked pairs, the old ones copied
// over, the rest zero (a new block, as Array.new makes it).
static void nt_grow(Nt* x) {
  u64 words = (u64)x->cap * 8;
#ifdef TEL_IC_STANDALONE
  u32* m = realloc(x->m, words * 2 * 4);
  if (m == NULL) {
    abort();
  }
  x->m = m;
  memset(x->m + words, 0, words * 4);
#else
  u32 c = 0;
  while ((1ull << c) < words) {
    c += 1;
  }
  c += 1;
  u64 loc = heap_alloc(x->e, c - 1);
  u32* m = (u32*)blk_ptr(x->e.mem, loc, 0);
  memcpy(m, x->m, words * 4);
  memset(m + words, 0, words * 4);
  blk_free(x->e, x->mt);
  x->mt  = term_blk(false, c, loc);
  x->m   = m;
#endif
  x->cap = x->cap * 2;
}

// alloc: the last agent freed, else the next unused one.
static inline u32 nt_alloc(Nt* x, u32 k, u32 a, u32 b) {
  u32 id;
  if (x->free != 0) {
    id = x->free;
    x->free = x->m[id * 8 + 1];
  } else {
    if (x->bump >= x->cap) {
      nt_grow(x);
    }
    id = x->bump;
    x->bump = id + 1;
  }
  x->m[id * 8]     = k;
  x->m[id * 8 + 4] = a;
  x->m[id * 8 + 5] = b;
  return id;
}

// delete: the agent's kind cleared, and it heads the free list.
static inline void nt_delete(Nt* x, u32 n) {
  x->m[n * 8 + 1] = x->free;
  x->m[n * 8]     = 0;
  x->free         = n;
}

static inline void nt_push(Nt* x, u32 a, u32 b) {
  if (x->sp >= x->cap) {
    nt_grow(x);
  }
  x->m[x->sp * 8 + 6] = a;
  x->m[x->sp * 8 + 7] = b;
  x->sp += 1;
}

// connect: p wired to q; two principal ports meeting are an active pair.
static inline void nt_connect(Nt* x, u32 p, u32 q) {
  x->m[NT_IDX(p)] = q;
  x->m[NT_IDX(q)] = p;
  if ((p & 3) == 0 && (q & 3) == 0) {
    u32 a = p >> 2;
    u32 b = q >> 2;
    if (x->m[a * 8] > 2 && x->m[b * 8] > 2) {
      nt_push(x, a, b);
    }
  }
}

// spend: one interaction, or the error that fuel ran out.
static inline void nt_spend(Nt* x) {
  if (x->fuel == 0) {
    x->err = 1;
  } else {
    x->fuel -= 1;
  }
}

static inline void nt_del2(Nt* x, u32 n, u32 m) {
  nt_delete(x, n);
  nt_delete(x, m);
}

static inline void nt_fail(Nt* x, u32 why) {
  x->err = 2;
  x->why = why;
}

// Instantiation (IC.bend's `instantiate`; the store's layout is described
// there).
static inline u32 nt_tr(Nt* x, u32 p, u32 e, u32 env, u32 res, u32 map) {
  if ((p >> 2) == e) {
    return (p & 3) == 0 ? env : res;
  }
  return x->t[map + (p >> 2)] * 4 + (p & 3);
}

static void nt_instantiate(Nt* x, u32 tid, u32 env, u32 res) {
  u32* t   = x->t;
  u32 map  = t[1];
  u32 off  = t[2 + tid];
  u32 k    = t[off];
  u32 e    = t[off + 1];
  u32 l    = t[off + 2];
  u32 w    = t[off + 3];
  u32 base = x->label;
  x->label += l;
  for (u32 i = 0; i < k; i += 1) {
    if (i != e) {
      u32 at = off + 4 + 3 * i;
      u32 kk = t[at];
      t[map + i] = nt_alloc(x, kk, kk == NT_DUP ? t[at + 1] + base : t[at + 1], t[at + 2]);
    }
  }
  u32 at = off + 4 + 3 * k;
  for (u32 j = 0; j < w; j += 1, at += 2) {
    u32 p = nt_tr(x, t[at], e, env, res, map);
    u32 q = nt_tr(x, t[at + 1], e, env, res, map);
    nt_connect(x, p, q);
  }
}

// Guided copying (IC.bend's `region`): copy what the shapes vouch for and
// is materialized, agent by agent, a Dup of label l at every frontier.

#define NT_JOB_PAIR 0xFFFFFFFFu

static void nt_job(Nt* x, u32 s, u32 p) {
  if (x->jn + 2 > x->jcap) {
    x->jcap = x->jcap ? x->jcap * 2 : 256;
    x->js = realloc(x->js, x->jcap * sizeof(u32));
  }
  x->js[x->jn]     = s;
  x->js[x->jn + 1] = p;
  x->jn += 2;
}

static void nt_val(Nt* x, u32 v) {
  if (x->vn + 1 > x->vcap) {
    x->vcap = x->vcap ? x->vcap * 2 : 256;
    x->vs = realloc(x->vs, x->vcap * sizeof(u32));
  }
  x->vs[x->vn] = v;
  x->vn += 1;
}

static void nt_region(Nt* x, u32 l) {
  while (x->jn > 0) {
    x->jn -= 2;
    u32 s = x->js[x->jn];
    u32 p = x->js[x->jn + 1];
    if (s == NT_JOB_PAIR) {
      if (x->vn < 4) {
        nt_fail(x, NT_WHY_PAIR);
        x->jn = 0;
        return;
      }
      u32 b1 = x->vs[x->vn - 1];
      u32 b2 = x->vs[x->vn - 2];
      u32 a1 = x->vs[x->vn - 3];
      u32 a2 = x->vs[x->vn - 4];
      x->vn -= 4;
      u32 p1 = nt_alloc(x, NT_PAIR, 0, 0);
      u32 p2 = nt_alloc(x, NT_PAIR, 0, 0);
      nt_connect(x, p1 * 4 + 1, a1);
      nt_connect(x, p1 * 4 + 2, b1);
      nt_connect(x, p2 * 4 + 1, a2);
      nt_connect(x, p2 * 4 + 2, b2);
      nt_val(x, p2 * 4);
      nt_val(x, p1 * 4);
      continue;
    }
    u32 tag = x->t[s];
    u32 n   = p >> 2;
    u32 k   = NT_K(x, n);
    bool material = (p & 3) == 0;
    if (material && (k == NT_CONST || (tag == 1 && k == NT_ZERO) || (tag == 2 && k == NT_REF))) {
      u32 a = NT_A(x, n);
      u32 b = NT_B(x, n);
      nt_delete(x, n);
      u32 c1 = nt_alloc(x, k, a, b);
      u32 c2 = nt_alloc(x, k, a, b);
      nt_val(x, c2 * 4);
      nt_val(x, c1 * 4);
    } else if (material && k == NT_PAIR && (tag == 1 || tag == 4)) {
      u32 s1 = tag == 1 ? s : s + 2;
      u32 s2 = tag == 1 ? s : x->t[s + 1];
      u32 q1 = NT_P1(x, n);
      u32 q2 = NT_P2(x, n);
      nt_delete(x, n);
      nt_job(x, NT_JOB_PAIR, 0);
      nt_job(x, s2, q2);
      nt_job(x, s1, q1);
    } else {
      u32 d = nt_alloc(x, NT_DUP, l, 0);
      nt_connect(x, d * 4, p);
      nt_val(x, d * 4 + 2);
      nt_val(x, d * 4 + 1);
    }
  }
}

// The rules
// ---------

// A pair is (n, i) meeting (m, j), n first, as IC.bend's apply.rule has it.
typedef struct {
  u32 k, a, b, p1, p2;
} NtI;

static inline NtI nt_info(Nt* x, u32 n) {
  NtI i = {NT_K(x, n), NT_A(x, n), NT_B(x, n), NT_P1(x, n), NT_P2(x, n)};
  return i;
}

static void nt_dup_closure(Nt* x, u32 s, u32 n, NtI i, u32 m) {
  nt_spend(x);
  nt_delete(x, n);
  x->jn = 0;
  x->vn = 0;
  nt_job(x, s, m * 4);
  nt_region(x, i.a);
  if (x->vn < 2) {
    nt_fail(x, NT_WHY_COPIES);
    return;
  }
  u32 c1 = x->vs[x->vn - 1];
  u32 c2 = x->vs[x->vn - 2];
  nt_connect(x, c1, i.p1);
  nt_connect(x, c2, i.p2);
}

// A constant's part, word w: 0 as itself, a pair as a constant.
static inline u32 nt_const_node(Nt* x, u32 w) {
  return w == 0 ? nt_alloc(x, NT_ZERO, 0, 0) : nt_alloc(x, NT_CONST, w, 0);
}

// plan.of: where the plan of a pair headed at port p is, when p is a
// materialized code pointer whose code has one; else 0.
static inline u32 nt_plan_of(Nt* x, u32 p) {
  u32 h = p >> 2;
  if ((p & 3) == 0 && NT_K(x, h) == NT_REF) {
    return x->t[2 + x->t[0] + NT_A(x, h)];
  }
  return 0;
}

// <generated rules>
static void nt_dup_pair(Nt* x, u32 n, NtI i, u32 m, NtI j) {
  nt_spend(x);
  nt_del2(x, n, m);
  u32 p1 = nt_alloc(x, NT_PAIR, 0, 0);
  u32 p2 = nt_alloc(x, NT_PAIR, 0, 0);
  u32 dl = nt_alloc(x, NT_DUP, i.a, 0);
  u32 dr = nt_alloc(x, NT_DUP, i.a, 0);
  nt_connect(x, dl * 4, j.p1);
  nt_connect(x, dr * 4, j.p2);
  nt_connect(x, p1 * 4 + 1, dl * 4 + 1);
  nt_connect(x, p1 * 4 + 2, dr * 4 + 1);
  nt_connect(x, p2 * 4 + 1, dl * 4 + 2);
  nt_connect(x, p2 * 4 + 2, dr * 4 + 2);
  nt_connect(x, p1 * 4, i.p1);
  nt_connect(x, p2 * 4, i.p2);
}

// Inlined into its one caller: passed on the stack, the two infos cost a
// store-forwarding stall each (P8 N2: 15% of a run).
static inline __attribute__((always_inline)) void nt_apply(Nt* x, u8 r, u32 n, NtI i, u32 m, NtI j) {
  switch (r) {
    case NT_SETENV_PAIR: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 ap = nt_alloc(x, NT_APPLY, 0, 0);
      nt_connect(x, ap * 4, j.p1);
      nt_connect(x, ap * 4 + 1, j.p2);
      nt_connect(x, ap * 4 + 2, i.p1);
      return;
    }
    case NT_PASS: {
      nt_spend(x);
      nt_delete(x, n);
      nt_connect(x, m * 4, i.p1);
      return;
    }
    case NT_APPLY_REF: {
      nt_spend(x);
      nt_del2(x, n, m);
      nt_instantiate(x, j.a, i.p1, i.p2);
      return;
    }
    case NT_AWAIT_GATE: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 sc = nt_alloc(x, NT_SCRUT, 0, 0);
      nt_connect(x, sc * 4, i.p1);
      nt_connect(x, sc * 4 + 1, i.p2);
      return;
    }
    case NT_PASS_APP: {
      nt_spend(x);
      nt_delete(x, n);
      u32 e = nt_alloc(x, NT_ERA, 0, 0);
      nt_connect(x, e * 4, i.p1);
      nt_connect(x, m * 4, i.p2);
      return;
    }
    case NT_SELECT_GATE: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 sel = nt_alloc(x, NT_REF, 0, 4294967294u);
      nt_connect(x, sel * 4, i.p1);
      return;
    }
    case NT_SCRUT_PAIR: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 el = nt_alloc(x, NT_ERA, 0, 0);
      u32 er = nt_alloc(x, NT_ERA, 0, 0);
      nt_connect(x, el * 4, j.p1);
      nt_connect(x, er * 4, j.p2);
      u32 sel = nt_alloc(x, NT_REF, 1, 4294967293u);
      nt_connect(x, sel * 4, i.p1);
      return;
    }
    case NT_PROJECT_LEFT: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 e = nt_alloc(x, NT_ERA, 0, 0);
      nt_connect(x, e * 4, j.p2);
      nt_connect(x, j.p1, i.p1);
      return;
    }
    case NT_PROJECT_RIGHT: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 e = nt_alloc(x, NT_ERA, 0, 0);
      nt_connect(x, e * 4, j.p1);
      nt_connect(x, j.p2, i.p1);
      return;
    }
    case NT_SPLIT_PAIR: {
      nt_spend(x);
      nt_del2(x, n, m);
      nt_connect(x, j.p1, i.p1);
      nt_connect(x, j.p2, i.p2);
      return;
    }
    case NT_SPLIT_ZERO: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 c1 = nt_alloc(x, NT_ZERO, 0, 0);
      u32 c2 = nt_alloc(x, NT_ZERO, 0, 0);
      nt_connect(x, c1 * 4, i.p1);
      nt_connect(x, c2 * 4, i.p2);
      return;
    }
    case NT_SPLIT_ABORTED: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 l = x->label;
      x->label += 1;
      u32 dm = nt_alloc(x, NT_DUP, l, 0);
      nt_connect(x, dm * 4, j.p1);
      u32 a1 = nt_alloc(x, NT_ABORTED, j.a, 0);
      u32 a2 = nt_alloc(x, NT_ABORTED, j.a, 0);
      nt_connect(x, a1 * 4 + 1, dm * 4 + 1);
      nt_connect(x, a1 * 4, i.p1);
      nt_connect(x, a2 * 4 + 1, dm * 4 + 2);
      nt_connect(x, a2 * 4, i.p2);
      return;
    }
    case NT_SPLIT_STUCK: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 c1 = nt_alloc(x, NT_STUCK, j.a, 0);
      u32 c2 = nt_alloc(x, NT_STUCK, j.a, 0);
      nt_connect(x, c1 * 4, i.p1);
      nt_connect(x, c2 * 4, i.p2);
      return;
    }
    case NT_ERA_PAIR: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 el = nt_alloc(x, NT_ERA, 0, 0);
      u32 er = nt_alloc(x, NT_ERA, 0, 0);
      nt_connect(x, el * 4, j.p1);
      nt_connect(x, er * 4, j.p2);
      return;
    }
    case NT_ERA_ABORTED: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 e = nt_alloc(x, NT_ERA, 0, 0);
      nt_connect(x, e * 4, j.p1);
      return;
    }
    case NT_ERA_LEAF: {
      nt_spend(x);
      nt_del2(x, n, m);
      return;
    }
    case NT_DUP_PLANNED: {
      u32 s = nt_plan_of(x, j.p1);
      if (s == 0) {
        nt_dup_pair(x, n, i, m, j);
      } else {
        nt_dup_closure(x, s, n, i, m);
      }
      return;
    }
    case NT_DUP_ABORTED: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 a1 = nt_alloc(x, NT_ABORTED, j.a, 0);
      u32 a2 = nt_alloc(x, NT_ABORTED, j.a, 0);
      u32 dm = nt_alloc(x, NT_DUP, i.a, 0);
      nt_alloc(x, NT_ZERO, 0, 0);
      nt_connect(x, dm * 4, j.p1);
      nt_connect(x, a1 * 4 + 1, dm * 4 + 1);
      nt_connect(x, a2 * 4 + 1, dm * 4 + 2);
      nt_connect(x, a1 * 4, i.p1);
      nt_connect(x, a2 * 4, i.p2);
      return;
    }
    case NT_DUP_DUP: {
      nt_spend(x);
      nt_del2(x, n, m);
      if (i.a == j.a) {
        nt_connect(x, i.p1, j.p1);
        nt_connect(x, i.p2, j.p2);
      } else {
        u32 m1 = nt_alloc(x, NT_DUP, j.a, 0);
        u32 m2 = nt_alloc(x, NT_DUP, j.a, 0);
        u32 n1 = nt_alloc(x, NT_DUP, i.a, 0);
        u32 n2 = nt_alloc(x, NT_DUP, i.a, 0);
        nt_connect(x, m1 * 4, i.p1);
        nt_connect(x, m2 * 4, i.p2);
        nt_connect(x, n1 * 4, j.p1);
        nt_connect(x, n2 * 4, j.p2);
        nt_connect(x, m1 * 4 + 1, n1 * 4 + 1);
        nt_connect(x, m1 * 4 + 2, n2 * 4 + 1);
        nt_connect(x, m2 * 4 + 1, n1 * 4 + 2);
        nt_connect(x, m2 * 4 + 2, n2 * 4 + 2);
      }
      return;
    }
    case NT_DUP_LEAF: {
      nt_spend(x);
      nt_del2(x, n, m);
      u32 c1 = nt_alloc(x, j.k, j.a, j.b);
      u32 c2 = nt_alloc(x, j.k, j.a, j.b);
      nt_connect(x, c1 * 4, i.p1);
      nt_connect(x, c2 * 4, i.p2);
      return;
    }
    case NT_OPEN: {
      nt_spend(x);
      nt_delete(x, m);
      u32 v = nt_alloc(x, NT_PAIR, 0, 0);
      u32 cl = nt_const_node(x, x->t[j.a]);
      u32 cr = nt_const_node(x, x->t[j.a + 1]);
      nt_connect(x, v * 4 + 1, cl * 4);
      nt_connect(x, v * 4 + 2, cr * 4);
      nt_connect(x, v * 4, n * 4);
      return;
    }
  }
}
// </generated>

#ifndef TEL_IC_STANDALONE
// Is fi the step of an unbounded recursion (Core.bend's is.limit)?
static inline bool nt_limit(u32 fi) {
  return fi >= 0x80000000u && fi <= 0xFFFFFFF2u;
}
#endif

// The loop: pop, skip a stale pair, fire; stop when no pair is left, a
// rule failed, or the next pair is Bend's to fire (it stays stacked).
static void nt_reduce(Nt* x) {
  while (x->err == 0 && x->sp != 0) {
    u32 top = x->sp - 1;
    u32 a   = x->m[top * 8 + 6];
    u32 b   = x->m[top * 8 + 7];
    u32 ka  = x->m[a * 8];
    u32 kb  = x->m[b * 8];
    if (ka == 0 || kb == 0 || x->m[a * 8 + 1] != b * 4 || x->m[b * 8 + 1] != a * 4) {
      x->sp = top;
      continue;
    }
    if (ka >= NT_KINDS || kb >= NT_KINDS) {
      return;
    }
    u32 n = a;
    u32 m = b;
    u8  r = nt_rule[ka][kb];
    if (r == NT_NONE) {
      r = nt_rule[kb][ka];
      n = b;
      m = a;
    }
    if (r == NT_NONE || r == NT_BEND) {
      return;
    }
    NtI i = nt_info(x, n);
    NtI j = nt_info(x, m);
#ifndef TEL_IC_STANDALONE
    if (r == NT_APPLY_REF && nt_limit(j.b)) {
      return;
    }
#endif
    x->sp = top;
    nt_apply(x, r, n, i, m, j);
  }
}

#ifdef TEL_IC_STANDALONE
// The host's entry points. A control block is eight words: sp, bump, free,
// label, fuel, err, cap, why. The agents may move (grow): the block's new
// address comes back through m.

static Nt tel_ic_in(u32** m, u32* t, const u32* c) {
  Nt x = {0};
  x.m = *m;
  x.t = t;
  x.sp = c[0]; x.bump = c[1]; x.free = c[2]; x.label = c[3];
  x.fuel = c[4]; x.err = c[5]; x.cap = c[6]; x.why = c[7];
  return x;
}

static void tel_ic_out(Nt* x, u32** m, u32* c) {
  *m = x->m;
  c[0] = x->sp; c[1] = x->bump; c[2] = x->free; c[3] = x->label;
  c[4] = x->fuel; c[5] = x->err; c[6] = x->cap; c[7] = x->why;
  free(x->js);
  free(x->vs);
}

// Fire every pair it can: stops when none is left, a rule failed, or the top
// pair is one this file has no rule for (it stays stacked, for the host).
void tel_ic_reduce(u32** m, u32* t, u32* c) {
  Nt x = tel_ic_in(m, t, c);
  nt_reduce(&x);
  tel_ic_out(&x, m, c);
}

// A rule the host decided: n and k gone, one interaction spent, a stuck value
// numbered msg on r1 (and r2), and an eraser on each of e1, e2, e3. 0 is no
// port: agent 0 is never used.
void tel_ic_stuck(u32** m, u32* t, u32* c, u32 n, u32 k, u32 msg,
                  u32 r1, u32 r2, u32 e1, u32 e2, u32 e3) {
  Nt x = tel_ic_in(m, t, c);
  nt_del2(&x, n, k);
  nt_spend(&x);
  u32 rs[2] = {r1, r2};
  for (int i = 0; i < 2; i += 1) {
    if (rs[i] != 0) {
      nt_connect(&x, nt_alloc(&x, NT_STUCK, msg, 0) * 4, rs[i]);
    }
  }
  u32 es[3] = {e1, e2, e3};
  for (int i = 0; i < 3; i += 1) {
    if (es[i] != 0) {
      nt_connect(&x, nt_alloc(&x, NT_ERA, 0, 0) * 4, es[i]);
    }
  }
  tel_ic_out(&x, m, c);
}
#else
Term nt_reduce_run(Env e, Term* f, IoWork* w) {
  Nt x = {0};
  x.e  = e;
  x.mt = f[0];
  if (!blk_shr(f[0]) && !blk_shr(f[1])) {
    x.m     = (u32*)blk_ptr(e.mem, blk_loc(e.mem, f[0]), 0);
    x.t     = (u32*)blk_ptr(e.mem, blk_loc(e.mem, f[1]), 0);
    x.sp    = (u32)f[2];
    x.bump  = (u32)f[3];
    x.free  = (u32)f[4];
    x.label = (u32)f[5];
    x.fuel  = (u32)f[6];
    x.err   = (u32)f[7];
    x.cap   = (u32)f[8];
    nt_reduce(&x);
    free(x.js);
    free(x.vs);
  } else {
    // a shared block (BLK_SHR) is not ours to write: Bend fires them all
    x.sp = (u32)f[2]; x.bump = (u32)f[3]; x.free = (u32)f[4]; x.label = (u32)f[5];
    x.fuel = (u32)f[6]; x.err = (u32)f[7]; x.cap = (u32)f[8];
  }
  return io_tup(e, x.mt, io_tup(e, f[1], io_tup(e, (Term)x.sp, io_tup(e, (Term)x.bump,
         io_tup(e, (Term)x.free, io_tup(e, (Term)x.label, io_tup(e, (Term)x.fuel,
         io_tup(e, (Term)x.err, io_tup(e, (Term)x.cap, (Term)x.why)))))))));
}

static void __attribute__((constructor)) nt_reduce_use(void) {
  io_eff(CID(nt.reduce), nt_reduce_run);
}
#endif
