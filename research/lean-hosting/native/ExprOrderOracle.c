/* Lean4.33.1 native differential oracle; deliberately collide cached hashes.
 * Pinned source: library/expr_lt.cpp and kernel/level.cpp at819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
 * Generic constructors use the actual Expr/Level layout; no host comparator.
 */
#include <lean/lean.h>
#include <stdio.h>
extern void lean_initialize_runtime_module(void);
extern uint8_t lean_expr_quick_lt(lean_object*,lean_object*);
extern uint8_t lean_expr_lt(lean_object*,lean_object*);
static lean_object* word(unsigned tag,unsigned n,lean_object**fs,uint64_t data,int annotation){
 lean_object*x=lean_alloc_ctor(tag,n,annotation<0?8:16);
 for(unsigned i=0;i<n;i++){lean_inc(fs[i]);lean_ctor_set(x,i,fs[i]);}
 lean_ctor_set_uint64(x,n*sizeof(void*),data);
 if(annotation>=0)lean_ctor_set_uint8(x,n*sizeof(void*)+8,(uint8_t)annotation);
 return x;
}
static lean_object* plain(unsigned tag,unsigned n,lean_object**fs){
 lean_object*x=lean_alloc_ctor(tag,n,0);
 for(unsigned i=0;i<n;i++){lean_inc(fs[i]);lean_ctor_set(x,i,fs[i]);}return x;
}
#define W(tag,data,ann,...) word(tag,sizeof((lean_object*[]){__VA_ARGS__})/sizeof(void*),(lean_object*[]){__VA_ARGS__},data,ann)
#define P(tag,...) plain(tag,sizeof((lean_object*[]){__VA_ARGS__})/sizeof(void*),(lean_object*[]){__VA_ARGS__})
static lean_object* exprs[128];static const char*names[128];static unsigned count=0;
#define ADD(label,value) do{names[count]=label;exprs[count++]=(value);}while(0)
int main(void){
 lean_initialize_runtime_module();lean_object*z=lean_box(0),*one=lean_box(1);
 lean_object*nx=W(1,0,-1,z,lean_mk_string("x")),*ny=W(1,0,-1,z,lean_mk_string("y"));
 lean_object*nnum=W(2,0,-1,z,lean_box(2));
 lean_object*huge=lean_nat_mul(lean_box((size_t)1<<62),lean_box(16));
 lean_object*nhuge=W(2,0,-1,z,huge),*nxs=W(1,0,-1,nx,lean_mk_string("a"));
 lean_object*b0=W(0,0,-1,z),*b1=W(0,0,-1,one),*bx=W(0,0xffffffff,-1,z);
 lean_object*px=W(4,0,-1,nx),*py=W(4,0,-1,ny),*mx=W(5,0,-1,nx);
 lean_object*succ=W(1,((uint64_t)1<<40),-1,z),*deep=W(1,((uint64_t)2<<40),-1,succ);
 lean_object*maxxy=W(2,((uint64_t)1<<40),-1,px,py),*maxyx=W(2,((uint64_t)1<<40),-1,py,px);
 lean_object*imax=W(3,((uint64_t)1<<40),-1,px,py);
 ADD("bvar0",b0);ADD("bvar1",b1);ADD("bvar0-highhash",bx);ADD("bvar0-highbits",W(0,((uint64_t)255<<32),-1,z));
 ADD("fvar-x",W(1,0,-1,nx));ADD("fvar-y",W(1,0,-1,ny));ADD("fvar-num",W(1,0,-1,nnum));ADD("fvar-huge",W(1,0,-1,nhuge));ADD("fvar-prefix",W(1,0,-1,nxs));ADD("mvar-x",W(2,0,-1,nx));
 ADD("sort-zero",W(3,0,-1,z));ADD("sort-param-x",W(3,0,-1,px));ADD("sort-param-y",W(3,0,-1,py));ADD("sort-mvar-x",W(3,0,-1,mx));ADD("sort-succ",W(3,0,-1,succ));ADD("sort-deep",W(3,0,-1,deep));ADD("sort-max-xy",W(3,0,-1,maxxy));ADD("sort-max-yx",W(3,0,-1,maxyx));ADD("sort-imax",W(3,0,-1,imax));
 ADD("const-x-empty",W(4,0,-1,nx,z));ADD("const-y-empty",W(4,0,-1,ny,z));ADD("const-x-levelx",W(4,0,-1,nx,P(1,px,z)));ADD("const-x-levely",W(4,0,-1,nx,P(1,py,z)));ADD("const-x-levelxy",W(4,0,-1,nx,P(1,px,P(1,py,z))));
 ADD("app-01",W(5,0,-1,b0,b1));ADD("app-10",W(5,0,-1,b1,b0));ADD("app-00",W(5,0,-1,b0,b0));
 ADD("lam-x",W(6,0,0,nx,b0,b1));ADD("lam-y-info",W(6,0,2,ny,b0,b1));ADD("lam-domain",W(6,0,0,nx,b1,b0));ADD("lam-body",W(6,0,0,nx,b0,b0));ADD("forall",W(7,0,0,nx,b0,b1));
 ADD("let-false",W(8,0,0,nx,b0,b0,b1));ADD("let-true",W(8,0,1,nx,b0,b0,b1));ADD("let-name",W(8,0,0,ny,b0,b0,b1));ADD("let-type",W(8,0,0,nx,b1,b0,b1));ADD("let-value",W(8,0,0,nx,b0,b1,b1));ADD("let-body",W(8,0,0,nx,b0,b0,b0));
 ADD("nat-lit0",W(9,0,-1,P(0,z)));ADD("nat-lit-huge",W(9,0,-1,P(0,huge)));ADD("str-lit-a",W(9,0,-1,P(1,lean_mk_string("a"))));ADD("str-lit-unicode",W(9,0,-1,P(1,lean_mk_string("\xf0\x90\x80\x80"))));ADD("str-lit-private",W(9,0,-1,P(1,lean_mk_string("\xee\x80\x80"))));
 lean_object*int0=P(4,z),*int1=P(4,one),*dv0=P(3,z),*dv1=P(3,one);
 lean_object*kint0=P(1,P(0,nx,int0),z),*kint1=P(1,P(0,nx,int1),z);
 lean_object*knat0=P(1,P(0,nx,dv0),z),*knat1=P(1,P(0,nx,dv1),z);
 lean_object*md0=W(10,0,-1,kint0,b0),*md1=W(10,0,-1,kint1,b0);
 ADD("mdata-empty",W(10,0,-1,z,b0));ADD("mdata-nat0",W(10,0,-1,knat0,b0));ADD("mdata-nat1",W(10,0,-1,knat1,b0));ADD("mdata-body",W(10,0,-1,knat0,b1));ADD("mdata-int0",md0);ADD("mdata-int1",md1);
 ADD("app-incomparable-0",W(5,0,-1,md0,b0));ADD("app-incomparable-1",W(5,0,-1,md1,b1));
 lean_object*dvfalse=lean_alloc_ctor(1,0,1);lean_ctor_set_uint8(dvfalse,0,0);
 lean_object*dvtrue=lean_alloc_ctor(1,0,1);lean_ctor_set_uint8(dvtrue,0,1);
 ADD("mdata-string-a",W(10,0,-1,P(1,P(0,nx,P(0,lean_mk_string("a"))),z),b0));
 ADD("mdata-string-b",W(10,0,-1,P(1,P(0,nx,P(0,lean_mk_string("b"))),z),b0));
 ADD("mdata-bool-false",W(10,0,-1,P(1,P(0,nx,dvfalse),z),b0));
 ADD("mdata-bool-true",W(10,0,-1,P(1,P(0,nx,dvtrue),z),b0));
 ADD("mdata-name-x",W(10,0,-1,P(1,P(0,nx,P(2,nx)),z),b0));
 ADD("mdata-name-y",W(10,0,-1,P(1,P(0,nx,P(2,ny)),z),b0));
 ADD("mdata-syntax-missing",W(10,0,-1,P(1,P(0,nx,P(5,z)),z),b0));
 ADD("mdata-syntax-atom",W(10,0,-1,P(1,P(0,nx,P(5,P(2,z,lean_mk_string("atom")))),z),b0));
 ADD("mdata-int-tail0",W(10,0,-1,P(1,P(0,nx,int0),P(1,P(0,ny,dv0),z)),b0));
 ADD("mdata-int-tail1",W(10,0,-1,P(1,P(0,nx,int1),P(1,P(0,ny,dv1),z)),b0));
 ADD("proj-x0",W(11,0,-1,nx,z,b0));ADD("proj-y0",W(11,0,-1,ny,z,b0));ADD("proj-x1",W(11,0,-1,nx,one,b0));ADD("proj-body",W(11,0,-1,nx,z,b1));
 printf("{\"schema\":\"lean-expr-order-native/1\",\"commit\":\"819816b2e0a3bf405af45ae5c7af2491d8f5bee6\",\"names\":[");
 for(unsigned i=0;i<count;i++)printf("%s\"%s\"",i?",":"",names[i]);printf("],\"comparisons\":[");
 for(unsigned i=0;i<count;i++)for(unsigned j=0;j<count;j++)printf("%s[%u,%u,%u,%u]",i||j?",":"",i,j,lean_expr_quick_lt(exprs[i],exprs[j]),lean_expr_lt(exprs[i],exprs[j]));
 printf("]}\n");return 0;
}
