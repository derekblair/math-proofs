'use strict';
const perms=a=>a.length ? a.flatMap((x,i)=>perms(a.filter((_,j)=>i!==j)).map(t=>[x,...t])) : [[]];
let seed=91;const rng=m=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>11)%m;};
const check=(ok,s)=>{if(!ok)throw Error(s)};
let tables=0, permutations=0, pairs=0, rectangularTerms=0;
for(let n=2;n<=7;n++){
 const ix=Array.from({length:n},(_,i)=>i), P=perms(ix), N=n*(n-1);
 for(let rep=0;rep<15;rep++){
  const w=ix.map(()=>ix.map(()=>BigInt(1+rng(4)))), H=ix.map(()=>ix.map(()=>0n));
  for(let i=0;i+1<n;i+=2)for(let j=0;j+1<n;j+=2){
    const a=BigInt(rng(9)-4);H[i][j]=a;H[i+1][j]=-a;H[i][j+1]=-a;H[i+1][j+1]=a;
  }
  const records=P.map(p=>[p,p.reduce((a,j,i)=>a*w[i][j],1n),p.reduce((a,j,i)=>a+H[i][j],0n)]);
  const Z=records.reduce((z,[,v])=>z+v,0n), S=records.reduce((z,[,v,h])=>z+v*h,0n), Q=records.reduce((z,[,v,h])=>z+v*h*h,0n);
  let R=0n;
  for(let i=0;i<n;i++)for(let k=i+1;k<n;k++){
   const masses = ix.map(()=>ix.map(()=>0n));
   for(const [p,v] of records)masses[p[i]][p[k]]+=v;
   for(let j=0;j<n;j++)for(let l=0;l<n;l++)if(j!==l){
     check(BigInt(N*256)*masses[j][l]>=Z,"ordered-pair relabel ratio");
     pairs++;
     if(j<l){const d=H[i][j]+H[k][l]-H[i][l]-H[k][j];R+=d*d;rectangularTerms++;}
   }
  }
  const F=H.flat().reduce((a,b)=>a+b*b,0n);
  check(R===BigInt(n*n)*F,"rectangle centering");
  // A 1..4 product changes by at most 16 under a two-row orientation flip.
  // p(1-p) >=16/289; coupled marginal >=1/(256 n(n-1)).
  // Row pair probability >=1/n and unordered column pair probability >=2/(256 n(n-1)).
  const lhs=(Q*Z-S*S)*BigInt(256*289*(n-1));
  check(lhs>=32n*F*Z*Z,"conditional variance consequence");
  tables++;permutations+=P.length;
 }
}
console.log(JSON.stringify({tables,permutations,pairs,rectangularTerms}));
