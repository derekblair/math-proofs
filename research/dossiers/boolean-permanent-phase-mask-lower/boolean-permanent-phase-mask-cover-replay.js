
function permutations(values){
  if(!values.length)return [[]];
  return values.flatMap((v,i)=>permutations(values.filter((_,j)=>j!==i)).map(p=>[v,...p]));
}
function factorial(n){let ans=1n;for(let i=2;i<=n;i++)ans*=BigInt(i);return ans;}
let seed=314159265;
function rand(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;}
let tests=0, columnArrangements=0, equalityCases=0;
function check(n,K,patterns,orders){
  const k=Math.floor(n/2);
  let successes=0;
  for(const p of orders){
    if(patterns.every((row,pair)=>row[p[2*pair]]!==row[p[2*pair+1]]))successes++;
  }
  const probDen = BigInt(K)**BigInt(k) * factorial(2*k);
  const probNum = BigInt(K-1)**BigInt(k) * 4n**BigInt(k) * factorial(k)**2n;
  const left = BigInt(successes)*probDen;
  const right = BigInt(orders.length)*probNum;
  if(left>right) throw Error("violation");
  if(left===right)equalityCases++;
  tests++;
  columnArrangements+=orders.length;
}
for(let n=2;n<=8;n++){
  const orders=permutations(Array.from({length:n},(_,i)=>i));
  const k=Math.floor(n/2);
  for(const K of [2,3,4]){
    if(n<=4 && K<=3){
      for(let b=0;b<K**(n*k);b++){
        let z=b;
        const mat=Array.from({length:k},()=>Array.from({length:n},()=>{const x=z%K;z=Math.floor(z/K);return x;}));
        check(n,K,mat,orders);
      }
    }else{
      for(let b=0;b<40;b++){
        const mat=Array.from({length:k},()=>Array.from({length:n},()=>((rand()>>>12)%K)));
        check(n,K,mat,orders);
      }
    }
  }
}
console.log(JSON.stringify({tests,columnArrangements,equalityCases}));