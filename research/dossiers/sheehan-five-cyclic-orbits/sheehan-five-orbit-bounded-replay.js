"use strict";
const generator=(limit)=>{let f=[[[0,1,1],[0,1,-1]],[[2,0,-1],[4,3,1]],[[1,0,1],[4,4,1]],[[3,2,1],[3,2,-1]],[[1,3,-1],[2,4,-1]]];
const add=(v,i,e)=>v.map((x,j)=>x+(i===j?e:0));
let out=[];
for(let root=0;root<5;root++){
 const init=[root,[0,0,0,0,0]];
 function walk(P,red,k,cuts,adds){
  let [b,t]=P;
  if(k===0){if(b===root&&t.every(x=>!x)&&!(red===false))out.push([cuts,adds]);return;}
  if(red)for(let s of [1,-1]){let d=(b+s+5)%5,x=add(t,0,b===4&&s>0?1:b===0&&s<0?-1:0),R=s>0?[b,t]:[d,x];
 if(cuts.some(([a,u])=>a===R[0]&&u.join()===R[1].join()))continue;walk([d,x],false,k-1,[...cuts,R],adds);}
 else for(let [d,i,e] of f[b]){let x=add(t,i,e),R=[[b,t],[d,x]],key=R.map(([a,z])=>[a,...z].join()).sort().join(":");if(adds.some(r=>r[0]===key))continue;
 walk([d,x],true,k-1,cuts,[...adds,[key,...R]]);}
 }
 for(let k=2;k<=limit;k++)walk(init,true,2*k,[],[]);
}
let out2=new Map;
for(let [D,A]of out){let key=D.map(x=>x.join()).sort().join(";")+"||"+A.map(x=>x[0]).sort().join(";");if(!out2.has(key))out2.set(key,[D,A]);}
return [...out2.values()];
};
const alternative=(S,p,a,b,x,y)=>{let T=[1,a,b,x,y],m=z=>(z%p+p)%p;
function pos([v,u]){return 5*m(u.reduce((s,t,i)=>s+t*T[i],0))+v;}
for(let [D,A]of S){let C=D.map(pos).sort((a,b)=>a-b);if(new Set(C).size!==D.length)continue;
let W=A.map(([k,x,y])=>[pos(x),pos(y)]);if(new Set(W.map(w=>w.slice().sort().join())).size!==W.length)continue;
const piece=r=>{let n=C.findIndex(x=>x>=r);return n===-1||n===0?C.length-1:n-1;};
let P=C.map((_,i)=>i),root=i=>{while(P[i]!==i)i=P[i];return i;};for(let [u,v]of W)P[root(piece(u))]=root(piece(v));
if(P.every((_,i)=>root(i)===root(0)))return {cuts:C,added:W,K:C.length};}
};
const cert=generator(8);
const hist=cert.reduce((a,[x])=>(a[x.length]=(a[x.length]||0)+1,a),{});
const ok=(b,m)=>{if(!b)throw Error(m)};
ok(hist[4]===10&&hist[6]===30&&hist[8]===250&&cert.length===290,"universal circuit census");
function literal(p,a,b,x,y,R){
 let n=5*p, M=u=>(u%p+p)%p;
 let G=Array.from({length:n},(_,v)=>new Set([(v+1)%n,(v+n-1)%n]));
 let rem=new Set(R.cuts);
 for(let u of rem){G[u].delete((u+1)%n);G[(u+1)%n].delete(u);}
 function residual(u,v){
  let i=u%5,j=v%5,l=u/5|0,r=v/5|0,d=M(r-l); if(i>j)return residual(v,u);
  return i===j?(i===0?(d===a||d===p-a):i===3&&(d===b||d===p-b)):i===1&&j===2?d===p-1:i===1&&j===4?d===x:i===2&&j===4&&d===y;
 }
 for(let [u,v] of R.added){ok(!G[u].has(v)&&residual(u,v),"actual residual edge");G[u].add(v);G[v].add(u);}
 ok(G.every(e=>e.size===2),"actual degree 2");
 let seen=new Set([0]),Q=[0];
 while(Q.length)for(let v of G[Q.pop()])if(!seen.has(v)){seen.add(v);Q.push(v);}
 ok(seen.size===n,"actual spanning cycle");
}
for(let p of [3,5,7,11,13,17,19,23,29,31]){
 let h={},bad=[],n=(p-1)/2;
 for(let a=1;a<=n;a++)for(let b=1;b<=n;b++)for(let x=0;x<p;x++)for(let y=0;y<p;y++){
  let R=alternative(cert,p,a,b,x,y);
  if(R){literal(p,a,b,x,y,R);h[R.K]=(h[R.K]||0)+1;}
  else bad.push([a,b,x,y]);
 }
 if(p===3)ok(JSON.stringify(bad)==="[[1,1,0,0],[1,1,2,2]]","p3 exception list");
 else ok(!bad.length,"uncovered profile in >3 field");
 console.log({p,h,bad});
}

for(const [x,W] of [[0,[0,1,2,3,4,5,6,7,9,8,13,14,12,11,10]],[2,[0,1,2,3,4,6,5,10,11,7,8,9,12,13,14]]]){
 let p=3,n=15,a=1,b=1,y=x,M=v=>(v%p+p)%p;
 let C=new Set(Array.from({length:n},(_,i)=>[i,(i+1)%n].sort((a,b)=>a-b).join()));
 let H=W.map((u,i)=>[u,W[(i+1)%n]]);
 const cuts=Array.from({length:n},(_,i)=>i).filter(i=>!H.some(([u,v])=>u===i&&v===(i+1)%n||v===i&&u===(i+1)%n));
 const added=H.filter(([u,v])=>!C.has([u,v].sort((a,b)=>a-b).join()));
 ok(added.length>0,"distinct residual p3 cycle");
 literal(p,a,b,x,y,{cuts,added});
}
console.log("The two p3 exceptions also have explicit second Hamilton cycles.");
