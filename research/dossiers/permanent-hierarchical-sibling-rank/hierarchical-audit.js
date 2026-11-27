'use strict';
const seq=n=>Array.from({length:n},(_,i)=>i);
let gen=8712645;function rnd(n){gen^=gen<<13;gen^=gen>>>17;gen^=gen<<5;return (gen>>>0)%n;}
const weight=()=>BigInt(rnd(5)-2);
function reference(A,L,R){
 const n=A.length;let answer=0n;
 function go(i,used,w){
  if(i===n){for(let j=0;j<n;j++)if(!(used>>j&1))w*=R[j];answer+=w;return;}
  go(i+1,used,w*L[i]);
  for(let j=0;j<n;j++)if(!(used>>j&1)&&A[i][j])go(i+1,used|1<<j,w*A[i][j]);
 }
 go(0,0,1n);return answer;
}
function make(n,depth){
 if(n<2||!depth)return {n,A:seq(n).map(()=>seq(n).map(weight))};
 const a=n>>1,b=n-a,left=make(a,depth-1),right=make(b,depth-1),u=seq(n).map(weight),v=seq(n).map(weight);
 const A=seq(n).map(i=>seq(n).map(j=>i<a&&j<a?left.A[i][j]:i>=a&&j>=a?right.A[i-a][j-a]:u[i]*v[j]));
 return {a,b,left,right,u,v,n,A};
}
function prepare(n){
 const D=2*n,F=[1n];for(let i=1;i<=D;i++)F.push(F.at(-1)*BigInt(i));
 const bin=(n,j)=>F[n]/F[j]/F[n-j], sign=j=>j%2?-1n:1n;
 const W=seq(D+1).map(i=>{
  let p=[1n];for(let j=0;j<=D;j++)if(i!==j){const q=Array(p.length+1).fill(0n);p.forEach((v,k)=>{q[k]-=BigInt(j)*v;q[k+1]+=v;});p=q;}
  return p.map(v=>v*sign(D-i)*bin(D,i));
 });
 return {D,F,bin,W,sign};
}
function evalTree(N,L,R,cache){
 if(!N.left)return reference(N.A,L,R);
 const key=L.join(',')+'|'+R.join(',');let C=cache.get(N);
 if(!C){C=new Map;cache.set(N,C);}if(C.has(key))return C.get(key);
 const {D,F,bin,sign,W}=prepare(N.n);let value=0n;
 for(let i=0;i<=N.a;i++)for(let j=0;j<=N.b;j++){
  // Two directed rank-one cross edges. i is limited by both endpoints.
  if(i>N.b||j>N.a)continue;
  const mult=[i,j,i,j], pts=[0,0,0,0], d=2*(i+j);
  let adv=0n;
  function evalGrid(k,w){
   if(k<4){const l=mult[k];for(let p=0;p<=l;p++){pts[k]=BigInt(p);evalGrid(k+1,w*sign(l-p)*bin(l,p));}return;}
   const [x,y,z,t]=pts;
   for(let h=0;h<=D;h++){
    const g=BigInt(h),coef=W[h][d];if(!coef)continue;
    const LL=L.slice(0,N.a).map((p,i)=>p+g*N.u[i]*x), LR=R.slice(0,N.a).map((p,i)=>p+g*N.v[i]*t);
    const RL=L.slice(N.a).map((p,i)=>p+g*N.u[i+N.a]*y), RR=R.slice(N.a).map((p,i)=>p+g*N.v[i+N.a]*z);
    adv+=w*coef*evalTree(N.left,LL,LR,cache)*evalTree(N.right,RL,RR,cache);
   }
  }
  evalGrid(0,1n);const den=F[D]*F[i]*F[j];if(adv%den)throw Error('integrality');value+=adv/den;
 }
 C.set(key,value);return value;
}
let size=0,strict=0;
for(const n of [2,3,4,5])for(let j=0;j<5;j++){
 const T=make(n,2),L=seq(n).map(weight),R=seq(n).map(weight);
 for(const [a,b]of [[L,R],[seq(n).map(()=>0n),seq(n).map(()=>0n)]]){
  const x=evalTree(T,a,b,new Map),y=reference(T.A,a,b);
  if(x!==y)throw Error('mismatch '+[n,j,x,y]);size++;if(x)strict++;
 }
}
console.log(JSON.stringify({profiles:size,nonzero:strict}));
