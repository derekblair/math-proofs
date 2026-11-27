"use strict";
const assert=require("node:assert/strict");
const range=n=>Array.from({length:n},(_,i)=>i);
function perms(a){return a.length?a.flatMap((x,i)=>perms(a.filter((_,j)=>i!==j)).map(t=>[x,...t])):[[]];}
function choose(n,k){if(k<0||k>n)return 0;let t=1;for(let i=1;i<=k;++i)t=t*(n-i+1)/i;return Math.round(t);}
const fac=n=>n<2?1:n*fac(n-1);
function expansion(n,q,p){
 const rows=range(q*n+1).map(()=>new Map);
 const columns=range(q*n+1).map(()=>new Map);
 for(const pi of perms(range(n))){
   const go=(i,u,v,d,c)=>{
     if(i===n){
       const uk=u.join(","),vk=v.join(","),cs=columns[d],rs=rows[d];
       if(!cs.has(vk))cs.set(vk,cs.size);
       if(!rs.has(uk))rs.set(uk,new Map);
       const r=rs.get(uk),j=cs.get(vk);
       r.set(j,((r.get(j)||0)+c)%p);
       return;
     }
     const id=i*n+pi[i];
     for(let s=0;s<=q;++s){
       const c1=c*choose(q,s)%p;if(!c1)continue;
       go(i+1,q-s?[...u,id+":"+ (q-s)]:u,s?[...v,id+":"+s]:v,d+s,c1);
     }
   };
   go(0,[],[],0,1);
 }
 return rows.map(row=>[...row.values()]);
}
function sparseRank(rows,p){
 const piv=new Map;
 const mod=x=>(x%p+p)%p;
 const inv=x=>{for(let j=1;j<p;++j)if(x*j%p===1)return j;throw Error("not a field");};
 for(const src of rows){
   const r=new Map([...src].filter(([,v])=>v));
   while(r.size){
     const i=Math.min(...r.keys()),v=r.get(i),a=piv.get(i);
     if(!a){const c=inv(v); for(const [j,w] of r)r.set(j,w*c%p);piv.set(i,r);break;}
     for(const [j,w] of a){const next=mod((r.get(j)||0)-v*w);if(next)r.set(j,next);else r.delete(j);}
   }
 }
 return piv.size;
}
function prediction(n,q,p,k){
 const S=range(q-1).map(x=>x+1).filter(x=>choose(q,x)%p);
 let r=0,A=[1];
 for(let a=0;a<=n;++a){
   for(let b=0;b<=n-a;++b)r+=choose(n,a)**2*fac(a)*choose(n-a,b)**2*(A[k-q*b]||0);
   const B=[];for(let i=0;i<A.length;++i)for(const s of S)if(A[i])B[i+s]=(B[i+s]||0)+A[i];A=B;
 }
 return r;
}
let total=0;
for(const p of [2,3,5,7,101])for(let n=0;n<=4;++n)for(let q=1;q<=5;++q){
 if(n===4&&q>=4)continue;
 const E=expansion(n,q,p);
 for(let k=0;k<=q*n;++k){assert.equal(sparseRank(E[k],p),prediction(n,q,p,k),[n,q,p,k].join(","));total++;}
}
console.log({exactCatalecticantRanks:total});
