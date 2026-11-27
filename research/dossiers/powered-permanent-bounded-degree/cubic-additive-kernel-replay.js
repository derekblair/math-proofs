'use strict';
const gen=a=>a.length?a.flatMap((x,i)=>gen(a.filter((_,j)=>i!==j)).map(p=>[x,...p])):[[]];
const rs=[];
for(let n=2;n<=4;n++){
 const I=Array.from({length:n},(_,i)=>i), perms=gen(I), E=I.flatMap(i=>I.filter(j=>i!==j).map(j=>[i,j])), allowed=new Map();
 const key=M=>E.map(([i,j])=>M[i][j]+1).join("");
 const dots=(M)=>perms.every(p=>p.reduce((s,j,i)=>s+M[i][j],0)===0);
 for(let k=0;k<3**E.length;k++){
   const M=I.map(()=>I.map(()=>0));let b=k;
   for(const [i,j] of E){M[i][j]=(b%3)-1;b=Math.floor(b/3);}
   if(!dots(M))continue;
   if(I.some(i=>I.some(j=>M[i][j]!==M[i][0]-M[j][0])))throw Error("additivity");
   allowed.set(key(M),M);
 }
 let independentPairs=0;
 const normalize=x=>((x+4)%3)-1, cs=[...allowed.values()].filter(A=>E.some(([i,j])=>A[i][j]!==0));
 for (let i=0;i<cs.length;i++)for(let j=i+1;j<cs.length;j++){
   const A=cs[i],B=cs[j];if(E.every(([a,b])=>A[a][b]===-B[a][b]))continue;
   independentPairs++;
   const C=I.map(a=>I.map(b=>normalize(A[a][b]+B[a][b])));
   const D=I.map(a=>I.map(b=>normalize(A[a][b]-B[a][b])));
   if(allowed.has(key(C))&&allowed.has(key(D)))throw Error("kernel dimension two");
 }
 rs.push({n,arrays:3**E.length,additive:allowed.size,independentPairs});
}
console.log(JSON.stringify(rs));