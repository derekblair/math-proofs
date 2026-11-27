const add=([a,b],[c,d])=>[a+c,b+d];
const mul=([a,b],[c,d])=>[a*c-b*d,a*d+b*c];
const norm=([a,b])=>a*a+b*b;
const one=[1n,0n], zero=[0n,0n], I=[0n,1n];
let seed=262193;
function rand(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return BigInt((seed>>>15)%7-3);}
function nonzeroGaussian(){const z=[rand(),rand()];return norm(z)?z:one;}
function gadget(m,u,v){
  const pattern=Array.from({length:m+2},()=>[]);
  pattern[0]=[...new Set([u,v])];
  pattern[1]=pattern[0].slice();
  for(let i=0;i<m;i++){
    if(i===u)pattern[i+2].push(m);
    if(i===v)pattern[i+2].push(m+1);
    if(i!==u&&i!==v)pattern[i+2].push(i);
  }
  return pattern;
}
function expand(pattern,S){
  let result=zero, p=0;const used=[];
  function rec(mask, sign, prod){
    if(used.length===pattern.length){result=add(result,prod.map(x=>x*sign));++p;return;}
    const row=used.length;
    for(const j of pattern[row]){
      if(mask&(1<<j))continue;
      const inversions=used.filter(x=>x>j).length;
      used.push(j);rec(mask|(1<<j),inversions%2?-sign:sign,mul(prod,S[row][j]));used.pop();
    }
  }
  rec(0,1n,one);return [p,norm(result)];
}
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){[a,b]=[b,a%b];}return a;}
function exactRank(M){
  const a=M.map(r=>r.slice());let rank=0;
  for(let col=0;col<a[0].length;col++){
    const pivot=a.findIndex((row,i)=>i>=rank&&row[col]!==0n);
    if(pivot<0)continue;
    [a[rank],a[pivot]]=[a[pivot],a[rank]];
    for(let row=rank+1;row<a.length;row++){
      const y=a[row][col];if(!y)continue;
      const x=a[rank][col];
      for(let j=col;j<a[0].length;j++)a[row][j]=x*a[row][j]-y*a[rank][j];
      const d=a[row].reduce(gcd,0n);
      if(d>1n)for(let j=col;j<a[0].length;j++)a[row][j]/=d;
    }
    rank++;
  }
  return rank;
}
let fixtures=0, evaluations=0, rankThree=0;
for(let m=2;m<=12;m++)for(let f=0;f<60;f++){
  const S=Array.from({length:m+2},()=>Array.from({length:m+2},nonzeroGaussian));
  for(let i=0;i<m;i++){
    const a=[rand(),0n], b=[rand(),0n];
    if(f%2===0){S[0][i]=a;S[1][i]=b;}
    else{
      // An invertible complex 2x2 row transformation of a real vector.
      S[0][i]=add(a,mul(I,b));
      S[1][i]=add(mul([2n,1n],a),b);
    }
  }
  for(let i=0;i<Math.min(m,f%4);i++)S[i+2][i]=zero;
  const table=Array.from({length:m},(_,u)=>Array.from({length:m},(_,v)=>{
    const [p,value]=expand(gadget(m,u,v),S);
    const product=Array.from({length:m},(_,i)=>i).filter(i=>i!==u&&i!==v)
      .reduce((a,i)=>a*norm(S[i+2][i]),1n);
    const diff=add(mul(S[0][u],S[1][v]),mul(S[0][v],S[1][u]).map(x=>-x));
    const expect=norm(S[u+2][m])*norm(S[v+2][m+1])*product*norm(diff);
    if(p!==(u===v?0:2)||value!==expect)throw Error("filler factor");
    ++evaluations;return value;
  }));
  const rank=exactRank(table);
  if(rank>3)throw Error("rank above three");
  if(rank===3)rankThree++;
  fixtures++;
}
const points=[zero,one,I,[2n,0n]];
const rankFour=exactRank(points.map(a=>points.map(b=>norm(add(a,b.map(c=>-c))))));
if(rankFour!==4)throw Error("expected independent complex directions");
let complexFixtures=0,complexEvaluations=0;
for(let m=5;m<=11;m++)for(let f=0;f<80;f++){
  const S=Array.from({length:m+2},()=>Array.from({length:m+2},()=>[rand(),rand()]));
  for(let i=0;i<Math.min(m,f%4);i++)S[i+2][i]=zero;
  const table=Array.from({length:m},(_,u)=>Array.from({length:m},(_,v)=>{
    const [p,value]=expand(gadget(m,u,v),S);
    if(p!==(u===v?0:2))throw Error("unexpected Boolean permanent");
    complexEvaluations++;return value;
  }));
  if(exactRank(table)>4)throw Error("complex rank above four");
  let M=0n,Ssum=0n;
  for(const row of table)for(const z of row){if(z>M)M=z;Ssum+=z;}
  const D=BigInt(m*(m-1))*M-Ssum, W=BigInt((m-1)**2);
  if(D*M*W+D*D+M*M<2n*BigInt(m-4)*M*M*W)throw Error("projection deficit");
  if(m===6&&100n*D<347n*M)throw Error("six-symbol deficit");
  complexFixtures++;
}
console.log({fixtures,evaluations,rankThree,rankFour,complexFixtures,complexEvaluations});
