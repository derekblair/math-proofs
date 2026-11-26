#include <array>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>
using Mat=std::array<std::array<int,6>,6>;
int p;
Mat one() { Mat m={}; for(int i=0;i<6;i++)m[i][i]=1; return m; }
Mat mul(Mat a,Mat b) {
 Mat m=one();
 for(int i=0;i<6;i++)for(int j=i+1;j<6;j++){
   int v=0;for(int k=i;k<=j;k++)v+=a[i][k]*b[k][j];
   m[i][j]=v%p;
 }
 return m;
}
Mat inv(Mat m) {Mat r=one(); for(int i=0;i<p-1;i++)r=mul(r,m); assert(mul(m,r)==one()); return r;}
Mat elem(std::array<int,5> t) {
  Mat r=one();for(int i=0;i<5;i++)r[i][i+1]=t[i]; return r;
}
Mat rim[2][2];
const int Back[3]={1,0,2};
struct Vert { int b; Mat m; };
uint64_t key(Vert x) {
 uint64_t s=x.b;
 for(int i=0;i<6;i++)for(int j=i+1;j<6;j++)s=s*p+x.m[i][j];
 return s;
}
Vert step(Vert v,int port) {if(port==2)return {1-v.b,v.m};return {v.b,mul(v.m,rim[v.b][port])};}
void enumerate(Vert v,int last,int n,int first){
 if(n==0){std::cout<<key(v)<<' '<<first<<'\n';return;}
 for(int q=0;q<3;++q)if(last<0||Back[last]!=q)
   enumerate(step(v,q),q,n-1,first<0?q:first);
}
int main(int argc,char**argv){
 p=17;
 rim[0][0]=elem({4,4,4,10,7});rim[0][1]=inv(rim[0][0]);
 rim[1][0]=elem({12,12,9,12,2});rim[1][1]=inv(rim[1][0]);
 enumerate({argc>1?atoi(argv[1]):0,one()},-1,16,-1);
}
