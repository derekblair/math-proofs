function perms(xs) {
  return xs.length ? xs.flatMap((x,i)=>perms(xs.filter((_,j)=>i!==j)).map(p=>[x,...p])) : [[]];
}
function factorial(n){let p=1n;for(let j=2;j<=n;j++)p*=BigInt(j);return p;}
let checkedSlices=0, checkedMatchingTerms=0, checkedBasis=0;
for(let n=2;n<=8;n++){
  const ps=perms(Array.from({length:n},(_,i)=>i));
  for(let a=1;a<=n;a++){
    const slice=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>
      i<a&&j>=a-1?BigInt((i*31-j*17)%19):i>=a&&j<a-1?0n:1n));
    let expected=0n;
    for(let i=0;i<a;i++)for(let j=a-1;j<n;j++)expected+=slice[i][j]**2n;
    expected*=factorial(a-1)*factorial(n-a);
    let observed=0n;
    for(const p of ps)observed+=p.reduce((v,c,r)=>v*slice[r][c]**2n,1n);
    if(observed!==expected)throw Error("Hall slice mismatch");
    checkedSlices++;
    checkedMatchingTerms+=ps.length;
  }
  const t=n-1;
  const id=Array.from({length:n},(_,i)=>i);
  for(let i=0;i<t;i++)for(let j=0;j<t;j++){
    const p=Array(n).fill(-1);p[i]=j;p[t]=t;
    const rows=id.filter(k=>k!==i&&k!==t);
    const cols=id.filter(k=>k!==j&&k!==t);
    rows.forEach((r,k)=>{p[r]=cols[k];});
    const q=p.slice();[q[i],q[t]]=[q[t],q[i]];
    for(let r=0;r<t;r++)for(let c=0;c<t;c++){
      if(Number(p[r]===c)-Number(q[r]===c)!==Number(r===i&&c===j))throw Error("basis mismatch");
    }
    checkedBasis++;
  }
}
console.log(JSON.stringify({checkedSlices,checkedMatchingTerms,checkedBasis}));