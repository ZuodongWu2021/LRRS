//#define DEBUG
#include "../signature/schnorr.hpp"
#include "../utility/print.hpp"
#include "../crypto/setup.hpp"
#include "../crypto/hash.hpp"
#include "../pke/elgamal.hpp"
#include "../mpc/pso/mqrpmt_psi.hpp"
#include "../crypto/ec_point.hpp"
#include "../crypto/ec_group.hpp"
#include "../commitment/pedersen.hpp"
#include <string>
#include<map>
#include<cmath>
using namespace std;
void test_schnorr(size_t TEST_NUM)
{
    std::cout << "begin the basic correctness test >>>" << std::endl; 
    
    Schnorr::PP pp = Schnorr::Setup(); 
    std::vector<ECPoint> pk(TEST_NUM); 
    std::vector<BigInt> sk(TEST_NUM);

    auto start_time = std::chrono::steady_clock::now(); 
    for(auto i = 0; i < TEST_NUM; i++){
        std::tie(pk[i], sk[i]) = Schnorr::KeyGen(pp); 
    }
    auto end_time = std::chrono::steady_clock::now(); 
    
    auto running_time = end_time - start_time;
    std::cout << "key generation takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count()/TEST_NUM << " ms" << std::endl;

    std::vector<Schnorr::SIG> sigma(TEST_NUM); 
    
    std::string message = "crypto is hard";  

    start_time = std::chrono::steady_clock::now(); 
    
    for(auto i = 0; i < TEST_NUM; i++){
        sigma[i] = Schnorr::Sign(pp, sk[i], message);
    }
    end_time = std::chrono::steady_clock::now(); 
    running_time = end_time - start_time;
    std::cout << "sign message takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count()/TEST_NUM << " ms" << std::endl;


    start_time = std::chrono::steady_clock::now(); 
    for(auto i = 0; i < TEST_NUM; i++){
        if(Schnorr::Verify(pp, pk[i], message, sigma[i]) == false){
            std::cout << "the " << i << "th verification fails" << std::endl;
        }
    }
    end_time = std::chrono::steady_clock::now(); 
    running_time = end_time - start_time;
    std::cout << "verify signature takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count()/TEST_NUM << " ms" << std::endl;
}

//my functions
std::string sha256(const std::string& str) {
    EVP_MD_CTX *mdctx;
    const EVP_MD *md;
    unsigned char md_value[EVP_MAX_MD_SIZE];
    unsigned int md_len;

    md = EVP_sha256();
    mdctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(mdctx, md, NULL);
    EVP_DigestUpdate(mdctx, str.c_str(), str.length());
    EVP_DigestFinal_ex(mdctx, md_value, &md_len);
    EVP_MD_CTX_free(mdctx);

    char hex[2 * md_len + 1];
    for (unsigned int i = 0; i < md_len; ++i) {
        sprintf(&hex[i * 2], "%02x", md_value[i]);
    }

    return std::string(hex, 2 * md_len);
}
struct PP
{
    ECPoint g; 
    std::vector<ECPoint> vec_h;  
    size_t N_max; 
};
PP Setup (size_t N_max)
{ 
    PP pp;
    pp.N_max = N_max;
    pp.g = ECPoint(generator); 
    /* 
    ** warning: the following method is ad-hoc and insafe cause it is not transparent
    ** we left a secure hash to many points mapping as the future work   
    */
    pp.vec_h = GenRandomECPointVector(N_max); 
    return pp; 
}

ECPoint Commit(PP &pp, std::vector<BigInt>& vec_m, BigInt r)
{
    if(pp.N_max < vec_m.size()){
        std::cerr << "message size is less than pp size" << std::endl;
    }
    size_t LEN = vec_m.size();
    std::vector<ECPoint> subvec_h(pp.vec_h.begin(), pp.vec_h.begin() + LEN);
    ECPoint commitment = pp.g * r + ECPointVectorMul(subvec_h, vec_m);
    return commitment;   
}

void keyGen(PP &com_pp,int num, std::vector<BigInt>& usk, std::vector<ECPoint>& upk,int index){
    for(int i = 0;i<index;i++){
        BigInt sk_user_int = GenRandomBigIntLessThan(order);
        ECPoint pk_user = com_pp.g*sk_user_int;
        usk[i] = sk_user_int;
        upk[i] = pk_user;
    }
    BigInt sk_user_int = GenRandomBigIntLessThan(order);
    ECPoint p = com_pp.g*sk_user_int;
    usk[index] = sk_user_int;
    upk[index] = p;
    for(int i = index+1;i<num;i++){
        BigInt sk_user_int = GenRandomBigIntLessThan(order);
        ECPoint pk_user = com_pp.g*sk_user_int;
        usk[i] = sk_user_int;
        upk[i] = pk_user;
    }
    upk[num] = com_pp.g;
}
ECPoint ecp_E;
    //Tag = h^sk,h = H(pk)
ECPoint genTag(BigInt usersk,ECPoint userpk){
    string E = sha256(userpk.ToByteString());
    ecp_E = Hash::StringToECPoint(E);
    ECPoint T = ecp_E*usersk;
    return T;
}
    //ELGamal enc C=(X,Y)
BigInt eLGamalEnc(PP &com_pp,ECPoint &X,ECPoint &Y, ECPoint userpk,ECPoint recoverpk){
    BigInt u = GenRandomBigIntLessThan(order); 
    X = com_pp.g*u;
    Y = recoverpk*u+userpk;
    return u;
}
ECPoint elGamalDec(BigInt recoversk, ECPoint X, ECPoint Y){
    ECPoint realsigner = Y-X*recoversk;
    return realsigner;
}
// void shizhuaner(int n,std::vector<BigInt> &lj,int index){
//     int i = 0;
//     std::vector<BigInt> ljt(n);
//     for(i=0; index>0; i++)    
//     {    
//         ljt[i]=BigInt(index%2);    
//         index= index/2;   
//     }  
//     int j = 0;
//     for(i=i-1 ;i>=0 ;i--)    
//     {    
//         lj[j++]=ljt[i];    
//     }
// }
vector<vector<BigInt> > shizhuaner(int n,int m){
    int i = 0;
    vector<vector<BigInt> > binary(m,vector<BigInt>(n));
    for(int i = 0;i<m;i++){
    	vector<int> t(n);
    	if(i==0){
    		for(int j = 0;j<n;j++){
    			binary[i][j] = 0UL;
			}
		}
		else{
			int temp = i;
    		for(int j =0; temp>0; j++)    
    		{    
       			binary[i][j] =temp%2;   
        		temp = temp/2;   
    		}  			
		}

	}
    
    return binary;
}
void genRandomNumber(int n, vector<BigInt> &rjs,vector<BigInt> &ajs,vector<BigInt> &sjs,vector<BigInt> &tjs,vector<BigInt> &rouks, vector<BigInt> &ljaj,vector<BigInt> lj){
    for(int j = 0;j<n;j++){
       BigInt rj_one = GenRandomBigIntLessThan(order); 
       rjs[j] = rj_one;
       BigInt aj_one = GenRandomBigIntLessThan(order);
       ajs[j] = aj_one;
       BigInt sj_one = GenRandomBigIntLessThan(order);
       sjs[j] = sj_one;
       BigInt tj_one = GenRandomBigIntLessThan(order);
       tjs[j] = tj_one;
       BigInt rouk_one = GenRandomBigIntLessThan(order);
       rouks[j] = rouk_one;
    }
    for(int g = 0;g<n;g++){
        ljaj[g] = lj[g]*ajs[g];
    }
}
void genCommit(PP &com_pp,vector<BigInt> rjs,vector<BigInt> ajs,vector<BigInt> sjs,vector<BigInt> tjs, vector<BigInt> ljaj,vector<BigInt> lj, std::vector<ECPoint> &Pederson_commitments_lj,std::vector<ECPoint> &Pederson_commitments_aj,std::vector<ECPoint> &Pederson_commitments_bj){
    for(int h = 0;h<rjs.size();h++){
    Pederson_commitments_lj[h] = com_pp.g*rjs[h]+com_pp.g*2*lj[h];
    Pederson_commitments_aj[h] = com_pp.g*sjs[h]+com_pp.g*2*ajs[h];
    Pederson_commitments_bj[h] = com_pp.g*tjs[h]+com_pp.g*2*ljaj[h];
    }
}
void genResponse(int n, std::vector<BigInt> &fj, std::vector<BigInt> &zaj, std::vector<BigInt> &zbj,vector<BigInt> lj,vector<BigInt> ajs,vector<BigInt> sjs,vector<BigInt> rjs,vector<BigInt> tjs,BigInt x){
    for(int j = 0;j<n;j++){
        fj[j] = lj[j]*x+ajs[j];
        zaj[j] = rjs[j]*x+sjs[j];
        zbj[j] = rjs[j]*(x-fj[j])+tjs[j];
    }
}
void string2map(const string &pA,map<int, int> &map_pA)
{
	string A = pA;

	for(int i = 0; i<A.size();i++)
	{
		if(A[i]=='('||A[i]==','||A[i]==')')
		{
			A[i]=' ';
		
		}	
	}
	//cout<<A<<endl;
	stringstream ss;
	ss << A;
	int temp;
	vector<int> A_string2_int;
	while(ss>>temp)
	{
		//cout << temp <<endl;
		A_string2_int.push_back(temp);

	}
	for(int j = 0; j <(int)A_string2_int.size()-1;j = j+2)
	{
		map_pA[A_string2_int[j+1]] = A_string2_int[j];	
	}
}

string multiplyPolynormial(const string &pA,const string &pB)
{
	map<int, int> map_pA; 
	map<int, int> map_pB; 
	map<int, int> map_ANS; //存放当前pA项乘以pB的结果
	map<int, int> map_ANS_total; //幂次相同的相加，为最终结果

	vector<int>map_ANS_total2vector;

	string2map(pA,map_pA);//string 存入map中 key:幂数，value：当前幂数的系数
	string2map(pB,map_pB);

	int n =  map_pA.size()+map_pB.size() + 1;

	for(int k = 0; k <n;k++ )//map初始化
	{
		map_ANS.insert(pair<int,int>(k,0));
		map_ANS_total.insert(pair<int,int>(k,0));
	
	
	}
	
	for(int i = 0; i < map_pA.size(); i++)
	{
		for(int j = 0; j < map_pB.size();j++ )
		{
			map_ANS[i+j] = map_pA[i]*map_pB[j];   
			map_ANS_total[i+j] = map_ANS_total[i+j] + map_ANS[i+j]; 
		
		}
			
	}

	//cout<<"the size of map_ANS_total is :"<<map_ANS_total.size()<<endl;
	int count = map_ANS_total.size();
	string answer;

	for(int m = 0; m < map_ANS_total.size();m++)//map转为string
	{
		count--;
		if(map_ANS_total[count]!=0)
		{
			char str[1000];
			sprintf(str,"(%d,%d)",map_ANS_total[count],count);
			//cout<<map_ANS_total[count]<<"  "<<count<<endl;
			answer = answer + str;
		}	
	}
	//cout<<answer<<endl;
	return answer;	
}
void Split(const std::string& src, const std::string& separator, std::vector<std::string>& dest) //字符串分割到数组
{
 
        //参数1：要分割的字符串；参数2：作为分隔符的字符；参数3：存放分割后的字符串的vector向量
 
	string str = src;
	string substring;
	string::size_type start = 0, index;
	dest.clear();
	index = str.find_first_of(separator,start);
	do
	{
		if (index != string::npos)
		{    
			substring = str.substr(start,index-start );
			dest.push_back(substring);
			start =index+separator.size();
			index = str.find(separator,start);
			if (start == string::npos) break;
		}
	}while(index != string::npos);
 
	//the last part
	substring = str.substr(start);
	dest.push_back(substring);
}
vector<vector<BigInt> > Pi;
//vector<vector<int> > Pi;
void chuli(string A,int m1,int n){
	string AA="";
	int size = 0;
	for(int i = 0;i<A.size();i++){
		if(A[i]=='('||A[i]==')')
		{
			if(A[i]==')'&&(i+1)<A.size()){
				AA+=",";
			}
			else{
				AA+="";				
			}

			size++;
		}
		else{
			AA+=A[i];
		}
	}
	//cout<<AA<<endl;
	vector<string> dest(size);
	Split(AA,",",dest);
	for(int i = 0;i<size;i+=2){
		int z = atoi(dest[i+1].c_str());
		if(z!=n){
			Pi[m1][z]=atoi(dest[i].c_str());
		}
	}
	//cout<<AA<<endl;
}

int main()
{  
    CRYPTO_Initialize(); 
    PP com_pp = Setup(128);
    int m=4;
	int n = sqrt(m);
    int index = 2;
    vector<BigInt> usk(m);   //user's sk
    vector<ECPoint> upk(m);  //user's pk
    keyGen(com_pp,m,usk,upk,index);
    BigInt signersk = usk[index];
    ECPoint signerpk = upk[index];
    ECPoint T = genTag(signersk,signerpk);

//recover pk and sk type:string
    BigInt sk_recover_int = GenRandomBigIntLessThan(order);
    ECPoint pk_recover = com_pp.g*sk_recover_int;
    
    ECPoint X;
    ECPoint Y;
    BigInt u = eLGamalEnc(com_pp,X,Y,signerpk,pk_recover);
    //ELGamal dec 
    ECPoint realsigner = elGamalDec(sk_recover_int,X,Y);
    
// (1) GenRandomNumber and compute commitments

    vector<vector<BigInt> > binary;
	binary = shizhuaner(n,m);
	BigInt temp = 0UL;
	for(int j = 0;j<m;j++){
		for (int i = 0; i < n/2; ++i) {
        	temp = binary[j][n-i-1];
        	binary[j][n-i-1] = binary[j][i];
       	 	binary[j][i] = temp;
    	}		
	}
    vector<BigInt> rjs(n);
    vector<BigInt> ajs(n);
    vector<BigInt> sjs(n);
    vector<BigInt> tjs(n);
    vector<BigInt> rouks(n);
    vector<BigInt> lj(n); // index = 2 binary= 10
    vector<BigInt> ljaj(n); 
    for(int i = 0;i<n;i++){
        lj[i] = binary[index][i];
    }
    //shizhuaner(n,lj,index);
    genRandomNumber(n,rjs,ajs,sjs,tjs,rouks,ljaj,lj);

    std::vector<ECPoint> Pederson_commitments_lj(n);
    std::vector<ECPoint> Pederson_commitments_aj(n);
    std::vector<ECPoint> Pederson_commitments_bj(n);
    genCommit(com_pp,rjs,ajs,sjs,tjs,ljaj,lj,Pederson_commitments_lj,Pederson_commitments_aj,Pederson_commitments_bj);


    for(int i = 0;i<m;i++){
		vector<BigInt> temp;
		for(int j = 0;j<n;j++){
			temp.push_back(0UL);
		}
		Pi.push_back(temp);
	}
    	for(int i = 0;i<m;i++){
		string A = "";
		if(binary[i][0]==1){
			if(binary[index][0]==1){
				A="(1,1),("+to_string(ajs[0].ToUint64())+",0)";				
			}
			else{
				A="(0,0),("+to_string(ajs[0].ToUint64())+",0)";					
			}
		}
		else{
			if(binary[index][0]==0UL){
				A="(1,1),(-"+to_string(ajs[0].ToUint64())+",0)";				
			}
			else{
				A="(0,0),(-"+to_string(ajs[0].ToUint64())+",0)";
			}
		}
		//cout<<A<<endl;
		for(int j = 1;j<n;j++){
			string B = "";
			if(binary[i][j]==1){
				if(binary[index][j]==1){
					B="(1,1),("+to_string(ajs[j].ToUint64())+",0)";
				}
				else{
					B="(0,0),("+to_string(ajs[j].ToUint64())+",0)";
				}
				
			}
			else{
				if(binary[index][j]==0UL){
					B="(1,1),(-"+to_string(ajs[j].ToUint64())+",0)";					
				}
				else{
					B="(0,0),(-"+to_string(ajs[j].ToUint64())+",0)";					
				}
			}
			A = multiplyPolynormial(A,B);
		}
		chuli(A,i,n);
    }
    std::vector<ECPoint> cdk1(n);
    for(int i = 0;i<n;i++){
        ECPoint t = upk[0]*Pi[0][i];
        for(int j = 1;j<m;j++){
            t+=upk[j]*Pi[j][i];
        }
        t +=com_pp.g*rouks[i];
        cdk1[i] = t;
    }
    std::vector<ECPoint> cdk2(n);
    for(int i = 0;i<n;i++){
        ECPoint t = T*Pi[0][i];
        for(int j = 1;j<m;j++){
            t+=T*Pi[j][i];
        }
        t +=ecp_E*rouks[i];
        cdk2[i] = t;
    }
    std::vector<ECPoint> cdk3(n);
    std::vector<ECPoint> C2(m+1);
    for(int i = 0;i<m;i++){
        C2[i] = Y-upk[i];
    }
    C2[m] = pk_recover;
    for(int i = 0;i<n;i++){
        ECPoint t = C2[0]*Pi[0][i];
        for(int j = 1;j<m;j++){
            t+=C2[j]*Pi[j][i];
        }
        t+=C2[m]*rouks[i];
        cdk3[i] = t;
    }

    //challenge
    BigInt x = GenRandomBigIntLessThan(order);
    std::vector<BigInt> fj(n);
    std::vector<BigInt> zaj(n);
    std::vector<BigInt> zbj(n);
    genResponse(n,fj,zaj,zbj,lj,ajs,sjs,rjs,tjs,x);
    //verify 1
    std::vector<ECPoint> zuo1(n);
    std::vector<ECPoint> you1(n);
    for(int i = 0;i<n;i++){
        zuo1[i] = Pederson_commitments_lj[i]*x+Pederson_commitments_aj[i];
        you1[i] = com_pp.g*zaj[i]+com_pp.g*2*fj[i];
        bool equal = zuo1[i].CompareTo(you1[i]);
        if(equal==false){
             std::cout << "verify fail"<<std::endl; 
        }
    }
    std::vector<BigInt> fjij(m);
    for(int i =0;i<m;i++){
        BigInt t = 0UL;
        if(binary[i][0]==1){
            t = fj[0];
        }
        else{
            t = x-fj[0];
        }
        for(int j = 1;j<n;j++){
            if(binary[i][j]==1){
                t=t*fj[j];
            }
            else{
                t=t*(x-fj[j]);
            }
        }
        fjij[i] = t;
    }
    ECPoint t1 = upk[0]*fjij[0];
    for(int i =1;i<m;i++){
        t1+=upk[i]*fjij[i];
    }
    ECPoint first = cdk1[0];
    for(int k=1;k<n;k++){
        BigInt tt=x;
        for(int i = 1;i<k;i++){
            tt=tt.Mul(x);
        }
       first+=cdk1[k]*tt;
    }
    BigInt mi=x;
        for(int i = 1;i<n;i++){
            mi=mi.Mul(x);
        }
    BigInt second = rouks[0];
    for(int k=1;k<n;k++){
        BigInt tt=x;
        for(int i = 1;i<k;i++){
            tt=tt.Mul(x);
        }
       second+=rouks[k]*tt;
    }
    ECPoint zuo3 = t1-first;
    BigInt zd = usk[index]*mi-second;
    ECPoint you3 = com_pp.g*zd;
    if(zuo3.CompareTo(you3)==true){
        std::cout << "verify success1"<<std::endl; 
    }
    ECPoint t12 = T*fjij[0];
    for(int i =1;i<m;i++){
        t12+=T*fjij[i];
    }
    ECPoint first2 = cdk2[0];
    for(int k=1;k<n;k++){
        BigInt tt=x;
        for(int i = 1;i<k;i++){
            tt=tt.Mul(x);
        }
       first2+=cdk2[k]*tt;
    }
    ECPoint zuo32 = t12-first2;
    ECPoint you32 = ecp_E*zd;
    if(zuo32.CompareTo(you32)==true){
        std::cout << "verify success2"<<std::endl; 
    }

    ECPoint t13 = C2[0]*fjij[0];
    for(int i =1;i<m;i++){
        t13+=C2[i]*fjij[i];
    }
    ECPoint first3 = cdk3[0];
    for(int k=1;k<n;k++){
        BigInt tt=x;
        for(int i = 1;i<k;i++){
            tt=tt.Mul(x);
        }
       first3+=cdk3[k]*tt;
    }
    ECPoint zuo33 = t13-first3;
    //BigInt zd = usk[2]*x*x;
    BigInt zd3 = u*mi-second;
    ECPoint you33 = pk_recover*zd;
    if(zuo33.CompareTo(you33)==true){
        std::cout << "verify success3"<<std::endl; 
    }
    CRYPTO_Finalize(); 
    
    return 0; 
}
