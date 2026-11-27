"use strict";
let seed=0x3e4dc811;
function pick(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>11)%n;}
function range(n){return Array.from({length:n},(_,i)=>i);}
function permutations(n){
  const out=[];
  function go(a,used){if(a.length===n){out.push(a);return;}
    for(const i of range(n))if(!used.includes(i))go([...a,i],[...used,i]);
  }
  go([],[]);return out;
}
function sign(p){let s=1n;for(let i=0;i<p.length;i++)for(let j=i+1;j<p.length;j++)if(p[i]>p[j])s=-s;return s;}
const perm=Array.from({length:6},(_,n)=>permutations(n).map(p=>[p,sign(p)]));
function det(A){return perm[A.length].reduce((sum,[p,s])=>sum+s*p.reduce((v,j,i)=>v*BigInt(A[i][j]),1n),0n);}
function minors(n,k){
  const out=[];
  function go(next,S){if(S.length===k){out.push(S);return;}
    for(let i=next;i<=n-k+S.length;i++)go(i+1,[...S,i]);
  }
  go(0,[]);return out;
}
function inverse(p){return p.map((_,j)=>p.indexOf(j));}
function words(n,q,call){
  function walk(prefix){if(prefix.length===n){call(prefix);return;}
    for(let i=0;i<q;i++)walk([...prefix,i]);
  }
  walk([]);
}
function add(map,key,value) {
  if(!value)return;
  const next=(map.get(key)??0n)+value;
  if(next)map.set(key,next);else map.delete(key);
}
function inputs(n,q,s,t) {
  const list=[];
  for(let i=0;i<n;i++){
    list.push([i,s[i],s[i]===t[i]?q:q-1]);
    if(s[i]!==t[i])list.push([i,t[i],1]);
  }
  return list;
}
function direct(factors,s,t){
  const n=s.length,q=factors.length,vars=inputs(n,q,s,t),base=q+1;
  const powers=vars.map((_,i)=>base**i);
  const key=vars.reduce((sum,v,i)=>sum+v[2]*powers[i],0);
  const components=factors.map(F=>{
    const poly=new Map();
    for(const [p,sgn] of perm[n]){
      function expand(i,c,e){
        if(i===n){add(poly,e,c);return;}
        for(let j=0;j<vars.length;j++){
          const [a,b,cap]=vars[j],value=F.values[i][a][b][p[i]];
          if(value&&Math.floor(e/powers[j])%base<cap){
            expand(i+1,c*BigInt(value),e+powers[j]);
          }
        }
      }
      expand(0,sgn,0);
    }
    return poly;
  });
  let product=new Map([[0,1n]]);
  for(const term of components){
    const next=new Map();
    for(const [a,v] of product)for(const [b,w] of term){
      if(vars.every((V,i)=>Math.floor(a/powers[i])%base+Math.floor(b/powers[i])%base<=V[2])){
        add(next,a+b,v*w);
      }
    }
    product=next;
  }
  return (product.get(key)??0n)*BigInt(q)**BigInt(s.filter((x,i)=>x===t[i]).length);
}
function split(F,selected,sInputs,tInputs){
  const n=sInputs.length,remaining=range(n).filter(i=>!selected.includes(i));
  let answer=0n;
  for(const output of minors(n,selected.length)){
    const rest=range(n).filter(i=>!output.includes(i));
    const a=det(selected.map(i=>output.map(j=>F.values[i][tInputs[i][0]][tInputs[i][1]][j])));
    const b=det(remaining.map(i=>rest.map(j=>F.values[i][sInputs[i][0]][sInputs[i][1]][j])));
    const parity=selected.reduce((v,x)=>v+x,0)+output.reduce((v,x)=>v+x,0);
    answer+=(parity%2?-1n:1n)*a*b;
  }
  return answer;
}
function mixed(factors,s,t){
  const n=s.length,q=factors.length,is=inverse(s),it=inverse(t);
  let sum=0n;
  words(n,q,assignment=>{
    const subsets=factors.map((_,a)=>range(n).filter(i=>assignment[i]===a));
    const selected=subsets.map((S,a)=>factors[a].col?S.map(i=>t[i]).sort((x,y)=>x-y):S);
    const sigmaMissing=range(n).map(i=>selected.reduce((total,S,a)=>
      total+Number(S.includes(factors[a].col?s[i]:i)),0));
    if(sigmaMissing.some(k=>k!==1))return;
    sum+=factors.reduce((value,F,a)=>{
      const first=range(n).map(i=>F.col?[is[i],i]:[i,s[i]]);
      const last=range(n).map(i=>F.col?[it[i],i]:[i,t[i]]);
      return value*split(F,selected[a],first,last);
    },1n);
  });
  return sum;
}
function local(n,col,degree){
  const lists=range(n).map(i=>[i,(i+1)%n].slice(0,degree));
  const values=range(n).map(slot=>range(n).map(i=>range(n).map(j=>range(n).map(()=>
    lists[slot].includes(col?j:i)?pick(5)-2:0))));
  return {lists,values,col};
}
function widerRows(factors,s,t){
  const n=s.length,q=factors.length,slots=range(n*q);
  const choices=slots.map(i=>factors[Math.floor(i/n)].lists[i%n]);
  let sum=0n;
  function go(chosen){
    if(chosen.length<choices.length){
      for(const raw of choices[chosen.length])if(chosen.filter(x=>x===raw).length<q)go([...chosen,raw]);
      return;
    }
    const groups=range(n).map(i=>slots.filter(j=>chosen[j]===i));
    words(n,q,word=>{
      const designated=groups.map((S,i)=>S[word[i]]);
      sum+=factors.reduce((v,F,a)=>{
        const selected=range(n).filter(slot=>designated.includes(a*n+slot));
        const first=range(n).map(i=>[chosen[a*n+i],s[chosen[a*n+i]]]);
        const last=range(n).map(i=>[chosen[a*n+i],t[chosen[a*n+i]]]);
        return v*split(F,selected,first,last);
      },1n);
    });
  }
  go([]);
  return sum;
}
const result={mixed:0,mixedNonzero:0,neighborhood:0,neighborhoodNonzero:0,target:0};
for(let trial=0;trial<150;trial++){
  const n=2+trial%3,q=2+Math.floor(trial/3)%3;
  const F=range(q).map((_,i)=>local(n,(trial+i)%3!==0,1));
  const s=perm[n][pick(perm[n].length)][0],t=perm[n][pick(perm[n].length)][0];
  const expected=direct(F,s,t);
  if(mixed(F,s,t)!==expected)throw Error("mixed factors "+[n,q,trial]);
  result.mixed++; if(expected)result.mixedNonzero++;
}
for(let trial=0;trial<35;trial++){
  const n=2+trial%2,q=2+Math.floor(trial/2)%2;
  const F=range(q).map(()=>local(n,false,2));
  const s=perm[n][pick(perm[n].length)][0],t=perm[n][pick(perm[n].length)][0];
  const expected=direct(F,s,t);
  if(widerRows(F,s,t)!==expected)throw Error("bounded raw-row neighborhoods "+[n,q,trial]);
  result.neighborhood++; if(expected)result.neighborhoodNonzero++;
}
for(const n of [2,3])for(const q of [2,3])for(const [s] of perm[n])for(const [t] of perm[n]){
  let actual=0n;
  for(const [p,sgn] of perm[n]){
    const values=range(n).map(i=>range(n).map(j=>range(n).map(k=>range(n).map(a=>Number(
      i===j&&k===p[i]&&a===p[i]
    )))));
    actual+=sgn**BigInt(q)*direct(Array(q).fill({values,col:false}),s,t);
  }
  if(actual!==(s.every((x,i)=>x===t[i])?BigInt(q)**BigInt(n):0n))
    throw Error("scaled permanent target coordinate");
  result.target++;
}

function supportedAffine(n,order,b){
  const descriptors=range(order).map(i=>range(b).map(j=>({raw:(i+j)%n,col:(i+j)%2})));
  const constant=range(order).map(()=>range(order).map(()=>pick(3)-1));
  const pieces=descriptors.map(list=>list.map(()=>range(n).map(()=>range(order).map(()=>pick(3)-1))));
  const values=range(order).map(slot=>range(n).map(i=>range(n).map(j=>range(order).map(o=>
    descriptors[slot].reduce((sum,{raw,col},k)=>
      sum+(col?(raw===j?pieces[slot][k][i][o]:0):(raw===i?pieces[slot][k][j][o]:0)),0)
  ))));
  return {order,descriptors,constant,pieces,values};
}
function affineDirect(factors,s,t){
  const n=s.length,q=factors.length,vars=inputs(n,q,s,t),base=q+1;
  const powers=vars.map((_,i)=>base**i);
  const target=vars.reduce((sum,v,i)=>sum+v[2]*powers[i],0);
  let product=new Map([[0,1n]]);
  for(const F of factors){
    const poly=new Map();
    for(const [p,sgn] of perm[F.order]){
      function expand(i,c,e){
        if(i===F.order){add(poly,e,c);return;}
        const constant=F.constant[i][p[i]];
        if(constant)expand(i+1,c*BigInt(constant),e);
        for(let j=0;j<vars.length;j++){
          const [a,b,cap]=vars[j],value=F.values[i][a][b][p[i]];
          if(value&&Math.floor(e/powers[j])%base<cap)expand(i+1,c*BigInt(value),e+powers[j]);
        }
      }
      expand(0,sgn,0);
    }
    const next=new Map();
    for(const [a,v] of product)for(const [b,w] of poly){
      if(vars.every((V,i)=>Math.floor(a/powers[i])%base+Math.floor(b/powers[i])%base<=V[2]))
        add(next,a+b,v*w);
    }
    product=next;
  }
  return (product.get(target)??0n)*BigInt(q)**BigInt(s.filter((x,i)=>x===t[i]).length);
}
function affineSplit(A,B,selected){
  const n=A.length,remaining=range(n).filter(i=>!selected.includes(i));
  let sum=0n;
  for(const U of minors(n,selected.length)){
    const W=range(n).filter(j=>!U.includes(j));
    const first=det(selected.map(i=>U.map(j=>B[i][j])));
    const last=det(remaining.map(i=>W.map(j=>A[i][j])));
    const parity=selected.reduce((v,x)=>v+x,0)+U.reduce((v,x)=>v+x,0);
    sum+=(parity%2?-1n:1n)*first*last;
  }
  return sum;
}
function affineFeature(factors,s,t){
  const n=s.length,q=factors.length,is=inverse(s),it=inverse(t),slots=[];
  for(let a=0;a<q;a++)for(let j=0;j<factors[a].order;j++)slots.push([a,j]);
  let sum=0n;
  function go(choice,count){
    if(choice.length<slots.length){
      const [a,j]=slots[choice.length],m=factors[a].descriptors[j].length;
      if(count+slots.length-choice.length>q*n)go([...choice,-1],count);
      if(count<q*n)for(let b=0;b<m;b++)go([...choice,b],count+1);
      return;
    }
    if(count!==q*n)return;
    const active=range(slots.length).filter(i=>choice[i]>=0);
    const descriptors=slots.map(([a,j],i)=>factors[a].descriptors[j][choice[i]]);
    function cover(indices,pInv,amount){
      const counts=range(n).map(()=>0);
      for(const i of indices){
        const {raw,col}=descriptors[i];
        counts[col?pInv[raw]:raw]++;
      }
      return counts.every(k=>k===amount);
    }
    for(const P of minors(active.length,n)){
      const tau=P.map(i=>active[i]),sigma=active.filter(i=>!tau.includes(i));
      if(!cover(tau,it,1)||!cover(sigma,is,q-1))continue;
      let value=1n;
      for(let a=0;a<q;a++){
        const F=factors[a],A=[],B=[],S=[];
        for(let i=0;i<slots.length;i++){
          const [a0,j]=slots[i];if(a0!==a)continue;
          if(choice[i]<0){A[j]=B[j]=F.constant[j];continue;}
          const {raw,col}=descriptors[i],part=F.pieces[j][choice[i]];
          A[j]=part[col?is[raw]:s[raw]];
          B[j]=part[col?it[raw]:t[raw]];
          if(tau.includes(i))S.push(j);
        }
        value*=affineSplit(A,B,S);
      }
      sum+=value;
    }
  }
  go([],0);
  return sum;
}
result.affine=0; result.affineNonzero=0;
for(let trial=0;trial<42;trial++){
  const n=2+trial%2,q=2,first=n+(trial%3===0?1:0),second=n+(trial%5===0?1:0);
  const F=[supportedAffine(n,first,2),supportedAffine(n,second,2)];
  const s=perm[n][pick(perm[n].length)][0],t=perm[n][pick(perm[n].length)][0];
  const expected=affineDirect(F,s,t);
  if(affineFeature(F,s,t)!==expected)throw Error("individual slot row/column affine locality");
  result.affine++;
  if(expected)result.affineNonzero++;
}

result.boolean=0; result.booleanNonzero=0;
for(let trial=0;trial<42;trial++){
  const n=2+trial%3,q=2;
  const F=[local(n,trial%3!==0,1),local(n,trial%3!==1,1)];
  const s=perm[n][pick(perm[n].length)][0],t=perm[n][pick(perm[n].length)][0];
  const support=inputs(n,q,s,t);
  let mobius=0n;
  for(let mask=0;mask<(1<<support.length);mask++){
    const present=support.filter((_,i)=>mask&(1<<i));
    const value=F.reduce((total,factor)=>{
      const A=range(n).map(i=>range(n).map(j=>present.reduce(
        (sum,[a,b])=>sum+factor.values[i][a][b][j],0)));
      return total*det(A);
    },1n);
    mobius+=((support.length-present.length)%2?-1n:1n)*value;
  }
  const shared=s.filter((x,i)=>x===t[i]).length;
  if(mobius*(2n**BigInt(shared))!==direct(F,s,t))throw Error("Boolean union-support coefficient");
  result.boolean++; if(mobius)result.booleanNonzero++;
}
console.log(JSON.stringify(result));
