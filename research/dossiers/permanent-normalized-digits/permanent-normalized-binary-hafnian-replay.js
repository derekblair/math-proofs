"use strict";
let seed=0x63e91aab;
function sample(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>11)%n;}
function factory(degree) {
  const zero=Array(degree).fill(0), one=[1,...zero.slice(1)];
  function norm(a,m){return ((a%m)+m)%m;}
  function red(a,u){return a.map(x=>norm(x,2**u));}
  function add(a,b,u){return red(a.map((x,i)=>x+b[i]),u);}
  function neg(a,u){return red(a.map(x=>-x),u);}
  function mul(a,b,u){
    const expanded=Array(2*degree-1).fill(0);
    for(let i=0;i<degree;i++)for(let j=0;j<degree;j++)expanded[i+j]+=a[i]*b[j];
    for(let i=expanded.length-1;i>=degree;i--){
      expanded[i-degree]-=expanded[i];expanded[i-degree+1]-=expanded[i];
    }
    return red(expanded.slice(0,degree),u);
  }
  function integer(a,u){return red(zero.map((_,i)=>i?0:a),u);}
  function scale(a,b,u){return mul(a,integer(b,u),u);}
  function equal(a,b){return a.every((x,i)=>x===b[i]);}
  function isUnit(a){return a.some(x=>x%2!==0);}
  function inverse(a,u){
    let y=one;
    for(let i=0;i<2**degree-2;i++)y=mul(y,a,u);
    const z=add(one,neg(mul(a,y,u),u),u);
    let series=one, power=one;
    for(let i=1;i<u;i++){power=mul(power,z,u);series=add(series,power,u);}
    const result=mul(y,series,u);
    if(!equal(mul(a,result,u),one))throw Error("nonunit inverse");
    return result;
  }
  function submatrix(A,removed){
    const kept=A.map((_,i)=>i).filter(i=>!removed.includes(i));
    return kept.map(i=>kept.map(j=>A[i][j]));
  }
  function haf(A,u){
    if(!u)return zero;
    if(!A.length)return one;
    const n=A.length, pivot=A[0].findIndex((x,j)=>j&&isUnit(x));
    let result=zero;
    if(pivot<0){
      for(let j=1;j<n;j++)result=add(result,mul(A[0][j],haf(submatrix(A,[0,j]),u-1),u),u);
      return result;
    }
    const indices=A.map((_,i)=>i);
    [indices[1],indices[pivot]]=[indices[pivot],indices[1]];
    const B=indices.map(i=>indices.map(j=>A[i][j]));
    const inv=inverse(B[0][1],u);
    for(let j=2;j<n;j++){
      const c=neg(mul(B[0][j],inv,u),u);
      if(equal(c,zero))continue;
      if(u>1)for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){
        if(a===1||a===j||b===1||b===j)continue;
        const weight=scale(mul(mul(c,B[1][a],u),B[1][b],u),2,u);
        result=add(result,neg(mul(weight,haf(submatrix(B,[1,j,a,b]),u-1),u),u),u);
      }
      for(let i=0;i<n;i++)if(i!==j)B[i][j]=B[j][i]=add(B[i][j],mul(c,B[i][1],u),u);
      if(!equal(B[0][j],zero))throw Error("pivot elimination");
    }
    return add(result,mul(B[0][1],haf(submatrix(B,[0,1]),u),u),u);
  }
  function brute(A,u){
    function visit(remaining){
      if(!remaining.length)return one;
      let result=zero;
      for(const j of remaining.slice(1)){
        const v=mul(A[remaining[0]][j],visit(remaining.filter(i=>i!==remaining[0]&&i!==j)),u);
        result=add(result,v,u);
      }
      return result;
    }
    return visit(A.map((_,i)=>i));
  }
  function lagrange(points,u){
    return points.map((a,i)=>{
      let poly=[one], denominator=one;
      for(let j=0;j<points.length;j++)if(i!==j){
        denominator=mul(denominator,add(a,neg(points[j],u),u),u);
        const next=Array(poly.length+1).fill(zero);
        for(let k=0;k<poly.length;k++){
          next[k]=add(next[k],neg(mul(points[j],poly[k],u),u),u);
          next[k+1]=add(next[k+1],poly[k],u);
        }
        poly=next;
      }
      const inv=inverse(denominator,u);
      return poly.map(x=>mul(x,inv,u));
    });
  }
  return {zero,one,integer,red,add,neg,mul,equal,haf,brute,lagrange};
}
let scalarCases=0, gridCases=0;
for(const d of [2,3]){
  const R=factory(d);
  for(let t=0;t<100;t++){
    const n=2+2*(t%5),u=1+(Math.floor(t/5)%4);
    const A=Array.from({length:n},()=>Array(n).fill(R.zero));
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
      A[i][j]=A[j][i]=R.red(Array.from({length:d},()=>sample(15)-7).map(x=>i===0&&t%3===0?2*x:x),u);
    }
    if(!R.equal(R.haf(A,u),R.brute(A,u)))throw Error("hafnian over unramified ring");
    scalarCases++;
  }
  for(let u=1;u<=4;u++){
    const n=2**d, nodes=Array.from({length:n},(_,i)=>Array.from({length:d},(_,j)=>(i>>j)&1));
    const weights=R.lagrange(nodes,u);
    const coefficients=Array.from({length:n},()=>Array.from({length:n},()=>R.integer(sample(23)-11,u)));
    const values=nodes.map(x=>nodes.map(y=>{
      let result=R.zero;
      for(let a=n-1;a>=0;a--){
        let at=R.zero;
        for(let b=n-1;b>=0;b--)at=R.add(R.mul(at,y,u),coefficients[a][b],u);
        result=R.add(R.mul(result,x,u),at,u);
      }
      return result;
    }));
    for(let a=0;a<n;a++)for(let b=0;b<n;b++){
      let result=R.zero;
      for(let i=0;i<n;i++)for(let j=0;j<n;j++){
        result=R.add(result,R.mul(values[i][j],R.mul(weights[i][a],weights[j][b],u),u),u);
      }
      if(!R.equal(result,coefficients[a][b]))throw Error("tensor Lagrange over lifted ring");
      gridCases++;
    }
  }
}
console.log(JSON.stringify({scalarCases,gridCases}));
