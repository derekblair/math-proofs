"use strict";
const assert=require("node:assert/strict");
const Pop=x=>{let t=0;while(x){x&=x-1;t++}return t};
function build(parts,t){let n=parts.reduce((s,x)=>s+x.length,0),A=[],z=0;
 for(let B of parts){for(let b of B){let u=b<<z;if(t)u|=((1<<n)-1)^(((1<<B.length)-1)<<z);A.push(u)}z+=B.length}
 return A}
function enumerate(N){let T=[[[],[]],[[[0]],[[0]]]];for(let n=2;n<=N;n++){T[n]=[[],[]];for(let t=0;t<2;t++){
 let atoms=[];for(let a=1;a<n;a++)for(let H of T[a][1-t])atoms.push(H);
 function f(j,r,L){if(!r){if(L.length>=2)T[n][t].push(build(L,t));return}for(let i=j;i<atoms.length&&atoms[i].length<=r;i++)f(i,r-atoms[i].length,L.concat([atoms[i]]))}
 f(0,n,[]);}}return T}
function inspect(A){let n=A.length,F=(1<<n)-1,L=Array(1<<n).fill(false),C=Array(1<<n).fill(false);
 for(let s=0;s<n;s++){let P=new Uint16Array(1<<n);P[1<<s]=1<<s;for(let m=1<<s;m<=F;m++)if(m&(1<<s)){
 let x=P[m];if(x)L[m]=true;
 if(x&A[s]&&Pop(m)>=3)C[m]=true;
 for(let z=x;z;z&=z-1){let u=31-Math.clz32(z&-z);for(let y=A[u]&~m;y;y&=y-1){let b=y&-y;P[m|b]|=b}}
 }}
 let c=Math.max(0,...C.map((f,i)=>f?Pop(i):0));if(!c)return [0,0,0];let marks=0,cuts=0,ores=0;
 function components(m){let sizes=[];while(m){let z=m&-m,S=z;m^=z;while(z){let u=z&-z,v=31-Math.clz32(u),w=A[v]&m;z^=u;m^=w;z|=w;S|=w}sizes.push(S)}return sizes;}
 let parts=Array.from({length:F+1},(_,s)=>components(F^s));
 const bestPath=new Uint8Array(F+1);
 for(let m=1;m<=F;m++) {
  if(L[m]) bestPath[m]=Pop(m);
  else for(let z=m;z;z&=z-1) bestPath[m]=Math.max(bestPath[m],bestPath[m^(z&-z)]);
 }
 let minOutside=n,maxLongest=0,cutThreshold=0;
 for(let x=0;x<=F;x++) if(C[x]){
  minOutside=Math.min(minOutside,bestPath[F^x]);
  if(Pop(x)===c)maxLongest=Math.max(maxLongest,bestPath[F^x]);
 }
 for(let s=1;s<=F;s++){
  const ps=parts[s].map(v=>bestPath[v]).sort((a,b)=>b-a),size=Pop(s);
  if(ps.length>size)cutThreshold=Math.max(cutThreshold,ps[size]);
 }
 // The theorem concerns k >= 2.
 const clamp=x=>Math.max(1,x);
 assert.equal(clamp(minOutside),clamp(maxLongest),JSON.stringify({A,minOutside,maxLongest}));
 assert.equal(clamp(maxLongest),clamp(cutThreshold),JSON.stringify({A,maxLongest,cutThreshold}));
 let conn=Math.min(n-1,...parts.map((A,s)=>A.length>=2?Pop(s):n));
 let degrees=A.map(Pop);
 for(let x=0;x<=F;x++)if(C[x]&&Pop(x)===c){
 let R=F^x,b=0;
 for(let z=R;z;z=(z-1)&R)if(L[z])b=Math.max(b,Pop(z));
 if(b<2)continue;marks++;
 for(let k=2;k<=b;k++){
 let found=false;for(let s=x;s;s=(s-1)&x){let ts=parts[s].filter(v=>bestPath[v]>=k).length;if(ts>=Pop(s)+1){found=true;break}}
 assert(found,JSON.stringify({A,x,k}));
 if(k<=conn){cuts++;let min=1e5;for(let s=0;s<=F;s++)if(Pop(s)===k+1){
  let d=0,ok=true;for(let z=s;z;z&=z-1){let i=31-Math.clz32(z&-z);if(A[i]&s){ok=false;break}d+=degrees[i]}if(ok)min=Math.min(min,d)
 }assert(min<n+k*(k-1));ores++}
 }}
 return [marks,cuts,ores]
}
const NN=10,T=enumerate(NN),ans=[];
for(let n=3;n<=NN;n++){let U=T[n][1],S=[0,0,0];for(let A of U){let r=inspect(A);for(let i=0;i<3;i++)S[i]+=r[i]}
 ans.push([n,U.length,...S])}
console.log(ans);