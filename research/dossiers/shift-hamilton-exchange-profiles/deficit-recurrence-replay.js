function test(m,D,limit){
  const s=D-1, ds=D-2, mod=i=>(i%m+m)%m;
  const groups=new Map;
  const inc=(map,k,w)=>map.set(k+":"+w,(map.get(k+":"+w)||0)+1);
  const dif=Array(m).fill(0), low=Array(m).fill(0), q=Array(m).fill(0);
  const types=Array.from({length:m},(_,i)=>Array.from({length:ds},(_,b)=>[i,b])).flat();
  const reps=Array.from({length:m},(_,i)=>i).filter(i=>{
    for(let j=mod(i+s);j!==i;j=mod(j+s))if(j<i)return false;
    return true;
  });
  let defectsChecked=0;
  function complete(t){
    defectsChecked++;
    for(let bits=0;bits<2**reps.length;bits++){
      const H=Array(m).fill(-1);let okay=true;
      for(let r=0;r<reps.length&&okay;r++){
        const p=reps[r];H[p]=(bits>>r)&1;
        let i=p;
        for(let j=mod(i+s);j!==p;j=mod(j+s)){
          H[j]=H[i]+dif[j];
          if(H[j]!==0&&H[j]!==1){okay=false;break;}
          i=j;
        }
        if(okay&&H[i]+dif[p]!==H[p])okay=false;
      }
      if(!okay||H.some((x,i)=>x+low[i]-q[i]<0||x+low[i]-q[i]>1))continue;
      const k=H.reduce((x,h,i)=>x+h+low[i],0);
      if(!k)continue;
      const num=k*s-t;
      if(num%m)throw Error("winding");
      inc(groups,k,num/m);
    }
  }
  function visit(start,t){
    complete(t);
    for(let j=start;j<types.length;j++){
      const [i,b]=types[j],weight=b||1;
      if(t+weight>limit)continue;
      if(!b){low[i]++;dif[i]--;dif[mod(i+s-1)]++;}
      else{q[i]++;dif[i]++;dif[mod(i+b)]--;}
      visit(j+1,t+weight);
      if(!b){low[i]--;dif[i]++;dif[mod(i+s-1)]--;}
      else{q[i]--;dif[i]--;dif[mod(i+b)]++;}
    }
  }
  visit(0,0);
  const expected=new Map,B=Array(m).fill(0);
  function brute(i,k,t){
    if(i===m){if(k)inc(expected,k,(k*s-t)/m);return;}
    for(let a=0;a<D;a++)for(let b=a+1;b<D;b++){
      const def=Number(a!==ds&&b!==ds)+(a<ds?a:0)+(b<ds?b:0);
      if(t+def>limit)continue;
      const u=mod(i+a),v=mod(i+b);
      if(B[u]===2||B[v]===2)continue;
      ++B[u];++B[v];brute(i+1,k+Number(a<ds)+Number(b<ds),t+def);--B[u];--B[v];
    }
  }
  brute(0,0,0);
  if(groups.size!==expected.size||[...groups].some(([k,v])=>expected.get(k)!==v))throw Error("incompatible counts");
  return {defectsChecked,factors:[...groups.values()].reduce((a,b)=>a+b,0),buckets:groups.size};
}
let cases=0,defectsChecked=0,factors=0,buckets=0;
for(let D=3;D<=6;D++)for(let m=D;m<=10;m++){
  const r=test(m,D,3);cases++;
  defectsChecked+=r.defectsChecked;factors+=r.factors;buckets+=r.buckets;
}
console.log({cases,defectsChecked,factors,buckets});
