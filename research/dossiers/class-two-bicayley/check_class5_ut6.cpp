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
std::unordered_multimap<uint64_t,uint64_t> hits;
std::vector<uint64_t> path;
bool dfs(Vert v,int last,int len,uint64_t w,int root) {
 if(!len){
   auto k=path.back(); auto it=hits.equal_range(k);
   for(auto i=it.first;i!=it.second;i++){
     auto other=i->second;
     bool sep=true;
     Vert z={root,one()};
     for(int t=0;t<(int)path.size()-2;t++){
       z=step(z,other%3); other/=3;
       if(std::find(path.begin()+1,path.end()-1,key(z))!=path.end()-1){sep=false;break;}
     }
     if(sep)return true;
   }
   uint64_t rev=0;for(int i=0;i<(int)path.size()-1;i++){rev=rev*3+w%3;w/=3;}
   hits.emplace(k,rev);
   return false;
 }
 for(int j=0;j<3;j++)if(last<0||Back[last]!=j){
   Vert z=step(v,j); uint64_t k=key(z);
   if(std::find(path.begin(),path.end(),k)!=path.end())continue;
   path.push_back(k);
   if(dfs(z,j,len-1,w*3+j,root)) return true;
   path.pop_back();
 }
 return false;
}
bool blocks(int h,int b) {
 hits.clear();path={key({b,one()})};
 return dfs({b,one()},-1,h,0,b);
}
bool word(std::string s) {
 Vert v={0,one()};std::vector<uint64_t> seen{key(v)};
 for(int i=0;i<(int)s.size();i++){
   v=step(v,s[i]-'0');auto k=key(v);
   if(i==(int)s.size()-1)return k==seen[0];
   if(std::find(seen.begin(),seen.end(),k)!=seen.end())return false;
   seen.push_back(k);
 }
 return false;
}

int main() {
 p=17;
 rim[0][0]=elem({4,4,4,10,7});rim[0][1]=inv(rim[0][0]);
 rim[1][0]=elem({12,12,9,12,2});rim[1][1]=inv(rim[1][0]);
 for(int h:{2,4,8,16})for(int b:{0,1}){
   if(blocks(h,b)){std::cout<<"Found forbidden simple cycle "<<2*h<<" "<<b<<"\n";return 1;}
   int duplicate=0;for(const auto &p:hits)if(hits.count(p.first)>1)duplicate++;
   std::cout<<h<<" "<<b<<" simple half-walk count "<<hits.size()<<" repeated-endpoint entries "<<duplicate<<"\n";
 }
 for(auto s:{"0020021121200212112002002121121200202112020021121120200202112112",
             "0020211202002112112020020211211200200211212002121120020021211212",
             "1200200212112120020021121200212112020020211211200202112020021121"})
   std::cout<<"C64 "<<word(s)<<" "<<s<<"\n";
}
