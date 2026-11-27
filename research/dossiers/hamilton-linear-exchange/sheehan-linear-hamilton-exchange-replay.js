"use strict";
const M=(x,m)=>(x%m+m)%m;
const key=(u,v)=>Math.min(u,v)+":"+Math.max(u,v);
const e=(i,j,m)=>[M(i,m),m+M(j,m)];
function base(m){return [[2,3],[0,1]].map(R=>Array.from({length:m},(_,i)=>R.map(r=>e(i,i+r,m))).flat());}
const graftEdges=m=>[e(0,2,m),e(1,1,m)];
function graph(m,odd){
 const H=base(m);
 if(odd) graftEdges(m).forEach(([u,v],c)=>{
  const k=key(u,v),i=H[c].findIndex(([a,b])=>key(a,b)===k);
  H[c].splice(i,1,[u,2*m],[v,2*m]);
 });
 return H;
}
function alternate(m,kind){
 let sched=[];
 if(kind==="ham"){
  if(m%2)sched=[[3,0],...Array.from({length:(m-3)/2},()=>[2,0])];
  else sched=[[3,0],...Array.from({length:(m-4)/2},()=>[2,0]),[2,1]];
 }else{
  sched=Array.from({length:Math.floor(m/3)},()=>[3,0]);
  if(m%3===1)sched.push([2,1]);
  if(m%3===2)sched.push([2,0]);
 }
 const C=new Map(base(m)[0].map(q=>[key(...q),q])),V=[new Set(),new Set()];
 let i=0;
 for(let [r,b] of sched){
  const j=M(i+r,m),i2=M(i+r-b,m);
  if(V[0].has(i)||V[1].has(j))throw Error("not simple alternating circuit");
  V[0].add(i);V[1].add(j);
  if(!C.delete(key(...e(i,j,m))))throw Error("not a red cut");
  const add=e(i2,j,m);if(C.has(key(...add)))throw Error("duplicate add");
  C.set(key(...add),add);i=i2;
 }
 if(i!==0)throw Error("not closed");
 return [...C.values()];
}
function verify(m,odd,W,c,kind){
 const H=graph(m,odd),n=2*m+odd;
 const R=new Set(H[c].map(e=>key(...e))),B=new Set(H[1-c].map(e=>key(...e)));
 const G=Array.from({length:n},()=>[]);
 let q=0,s=new Set;
 for(let [u,v] of W){
  const k=key(u,v);
  if(s.has(k)||!R.has(k)&&!B.has(k))throw Error("illegal witness edge");
  s.add(k);G[u].push(v);G[v].push(u);if(B.has(k))q++;
 }
 let goal=kind==="ham"?Math.floor(m/2):Math.ceil(m/3);
 if(G.some(row=>row.length!==2)||q!==goal)throw Error([m,odd,c,kind,"degree or distance",q,goal]);
 const Q=[0],A=new Set(Q);
 while(Q.length)for(let v of G[Q.pop()])if(!A.has(v)){A.add(v);Q.push(v);}
 if(kind==="ham"&&A.size!==n)throw Error("disconnected Hamilton");
}
let witnesses=0;
for(let m=4;m<=257;m++)for(let kind of ["ham","factor"])for(let c of [0,1]){
 let W=alternate(m,kind);
 if(c)W=W.map(([u,v])=>e(-u,3-(v-m),m));
 verify(m,0,W,c,kind);witnesses++;
 let [[a,b],[x,y]]=graftEdges(m);if(c)[a,b,x,y]=[x,y,a,b];
 let z;
 for(let t=0;t<m;t++){
  let Q=W.map(([u,v])=>e(u+t,v-m+t,m));
  if(Q.some(u=>key(...u)===key(a,b))&&!Q.some(u=>key(...u)===key(x,y))){
   z=Q.filter(u=>key(...u)!==key(a,b)).concat([[a,2*m],[b,2*m]]);
   break;
  }
 }
 if(!z)throw Error("no good graft translate");
 verify(m,1,z,c,kind);witnesses++;
}
function exhaust(m,odd){
 const n=2*m+odd, H=graph(m,odd), G=H.flatMap((L,c)=>L.map(([u,v])=>[u,v,c]));
 const by=Array.from({length:m},()=>[]), O=[];
 for(let [u,v,c] of G){
  if(v===2*m||u===2*m)O.push([u===2*m?v:u,c]);
  else by[u].push([v,c]);
 }
 let count=0,ham=0,D=[Infinity,Infinity],Dham=D.slice();
 function visit(O1,O2){
  const B=Array(m).fill(2),A=Array(m).fill(2),E=[];
  let blue=0;
  for(let o of [O1,O2])if(o){
   let [v,c]=o;if(v<m)A[v]--;else B[v-m]--;
   E.push([2*m,v]);blue+=c;
  }
  function go(i,k){
   if(i===m){
    if(B.some(v=>v!==0))return;
    count++;
    const L=Array.from({length:n},()=>[]);
    for(let [u,v] of E){L[u].push(v);L[v].push(u);}
    const Q=[0],S=new Set(Q);
    while(Q.length)for(let v of L[Q.pop()])if(!S.has(v)){S.add(v);Q.push(v);}
    const C=S.size===n;if(C)ham++;
    if(k){D[0]=Math.min(D[0],k);if(C)Dham[0]=Math.min(Dham[0],k);}
    if(k<n){D[1]=Math.min(D[1],n-k);if(C)Dham[1]=Math.min(Dham[1],n-k);}
    return;
   }
   function pick(j,t,s){
    if(t===0){go(i+1,k+s);return;}
    for(let k=j;k<by[i].length;k++){
     const [v,c]=by[i][k];if(!B[v-m])continue;
     B[v-m]--;E.push([i,v]);pick(k+1,t-1,s+c);E.pop();B[v-m]++;
    }
   }
   pick(0,A[i],0);
  }
  go(0,blue);
 }
 if(odd)for(let i=0;i<O.length;i++)for(let j=i+1;j<O.length;j++)visit(O[i],O[j]);else visit();
 if(D.some(x=>x!==Math.ceil(m/3))||Dham.some(x=>x!==Math.floor(m/2)))throw Error([m,odd,D,Dham]);
 return [n,count,ham,D,Dham];
}
const results=[];
for(let m=4;m<=9;m++)for(let o of [0,1])results.push(exhaust(m,o));
console.log({witnesses,results});
function general(m,D,kind){
 const d=D-2,k=kind==="ham"?Math.ceil((m-1)/d):Math.ceil(m/(d+1));
 let sched=[];
 if(kind==="ham"){
  const r=k*d+1-m;
  sched=[[d+1,0],...Array.from({length:k-2},()=>[d,0]),[d,r]];
 }else{
  const r=k*(d+1)-m;
  sched=Array.from({length:k-1},()=>[d+1,0]).concat([r===d?[d,d-1]:[d+1,r]]);
 }
 const H=Array.from({length:m},(_,i)=>[[i,M(i+d,m)],[i,M(i+d+1,m)]]).flat();
 const F=new Map(H.map(q=>[q.join(),q])),U=new Set,V=new Set;
 let i=0;
 for(let [r,b] of sched){
   const j=M(i+r,m),t=M(j-b,m);
   if(U.has(i)||V.has(j)||b<0||b>d-1||!F.delete([i,j].join()))throw Error("general noncycle");
   if(F.has([t,j].join()))throw Error("general duplicate");
   F.set([t,j].join(),[t,j]);U.add(i);V.add(j);i=t;
 }
 if(i!==0)throw Error("general no winding");
 const G=Array.from({length:2*m},()=>[]);let diff=0;
 for(let [x,y] of F.values()){
  const r=M(y-x,m);if(r>=D)throw Error("illegal general edge");
  if(r<d)diff++;
  G[x].push(m+y);G[m+y].push(x);
 }
 if(diff!==k||G.some(v=>v.length!==2))throw Error("general invalid spanning");
 if(kind==="ham"){
  const Q=[0],S=new Set(Q);
  while(Q.length)for(let v of G[Q.pop()])if(!S.has(v)){S.add(v);Q.push(v);}
  if(S.size!==2*m)throw Error("general not Hamilton");
 }
}
function exhaustGeneral(m,D){
 let B=Array(m).fill(2),P=[],mc=Infinity,mh=Infinity,count=0;
 function rec(i,k){
  if(i===m){
   if(B.some(Boolean))return;
   count++;if(!k)return;
   mc=Math.min(mc,k);
   let G=Array.from({length:2*m},()=>[]);
   for(let [u,v] of P){G[u].push(m+v);G[m+v].push(u);}
   let Q=[0],S=new Set(Q);while(Q.length)for(let v of G[Q.pop()])if(!S.has(v)){S.add(v);Q.push(v);}
   if(S.size===2*m)mh=Math.min(mh,k);
   return;
  }
  for(let r=0;r<D;r++)for(let s=r+1;s<D;s++){
   let v=M(i+r,m),w=M(i+s,m);if(!B[v]||!B[w])continue;
   P.push([i,v],[i,w]);B[v]--;B[w]--;
   rec(i+1,k+Number(r<D-2)+Number(s<D-2));
   B[v]++;B[w]++;P.pop();P.pop();
  }
 }
 rec(0,0);
 if(mc!==Math.ceil(m/(D-1))||mh!==Math.ceil((m-1)/(D-2)))throw Error([m,D,count,mc,mh]);
 return count;
}
let gw=0,ge=[];
for(let D=3;D<=13;D++)for(let m=D;m<=127;m++)for(let kind of ["ham","factor"]){general(m,D,kind);gw++;}
for(let D=3;D<=5;D++)for(let m=D;m<=8;m++) ge.push([m,D,exhaustGeneral(m,D)]);
console.log({gw,ge});