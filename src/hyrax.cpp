#undef NDEBUG
#include "hyrax.hpp"
#include <cmath>
using namespace std;
using namespace mcl::bn;

const int MAX_MSM_LEN=1e4;
const int COMM_OPT_MAX=65536; //don't optimize if larger than this
const int logmax=16;  /// max number=2^18-1
const int block_num=4;
inline G1 perdersen_commit(G1* g,ll* f,int n,G1* W)
{
    G1 ret;
    ret.clear();
    //timer t(true);
    //t.start();
    
    bool *used=new bool[COMM_OPT_MAX*block_num];
    memset(used,0,sizeof(bool)*COMM_OPT_MAX*block_num);
    for(int i=0;i<n;i++)
    {
            if(f[i]==0)
                continue;
            
            if(f[i]<0)
            {
                ll tmp=-f[i];
                for(int j=0;j<block_num;j++)
                {
                    ll fnow=(tmp>>(logmax*j))&65535;
                    W[fnow+(j<<logmax)]-=g[i];
                    used[fnow+(j<<logmax)]=1;
                }
                //W[-f[i]]-=g[i];
                //used[-f[i]]=1;
                //assert(-f[i]<COMM_OPT_MAX);
            }
            else
            {
                ll tmp=f[i];
                for(int j=0;j<block_num;j++)
                {
                    ll fnow=(tmp>>(logmax*j))&65535;
                    W[fnow+(j<<logmax)]+=g[i];
                    used[fnow+(j<<logmax)]=1;
                }
                //W[f[i]]+=g[i];
                //used[f[i]]=1;
                //assert(f[i]<COMM_OPT_MAX);
            }
    }
    //t.stop("add ",false);
    //const int logn=log2(COMM_OPT_MAX)+1;
    G1 gg[logmax*4];
    for(int j=0;j<logmax*4;j++)
        gg[j].clear();
    for(int j=0;j<COMM_OPT_MAX*block_num;j++)
    {
        if(used[j])
        {
            int jj=j%COMM_OPT_MAX;
            int blk=j/COMM_OPT_MAX;
            for(int k=0;k<logmax;k++)
            {
                if(jj&(1<<k))
                    gg[k+logmax*blk]+=W[j];
            }
            W[j].clear();
            used[j]=0;            
        }
    }
    for(int j=0;j<logmax*4;j++)
        ret+=gg[j]*(1<<j);
    //t.stop("accu",false);
    //t.stop("ALL: ",true);
    delete []used;
    return ret;
}
inline G1 perdersen_commit(G1* g,Fr* f,int n)
{
    G1 ret;
    G1::mulVec(ret,g,f,n);
    return ret;
}

Fr lagrange(Fr *r,int l,int k)
{
    assert(k>=0 && k<(1<<l));
    Fr ret=1;
    for(int i=0;i<l;i++)
    {
        if(k&(1<<i))
            ret*=r[i];
        else
            ret*=1-r[i];
    }
    return ret;
}
void brute_force_compute_LR(Fr* L,Fr* R,Fr* r,int l)
{
    int halfl=l/2,c=l-halfl;
    for(int k=0;k<(1<<halfl);k++)
        L[k]=lagrange(r,halfl,k);
    for(int k=0;k<(1<<c);k++)
        R[k]=lagrange(r+halfl,c,k);
}

Fr brute_force_compute_eval(Fr* w,Fr* r,int l)
{
    Fr ret=0;
    for(int k=0;k<(1<<l);k++)
        ret+=lagrange(r,l,k)*w[k];
    return ret;
}


G1 compute_Tprime(Fr* w,Fr* r,int l,G1* g,Fr* L,G1* Tk) 
{
    //w has 2^l length
    //assert(l%2==0);
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    G1 ret=perdersen_commit(Tk,L,rownum);
    return ret;
}

G1 compute_LT(Fr*w ,Fr*L,int l,G1*g,Fr*& ret) // L is row number length
{
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    Fr* res=new Fr[colnum];
    for(int j=0;j<colnum;j++)
    {
        res[j]=0;
        for(int i=0;i<rownum;i++)
            res[j]+=L[i]*w[i+j*rownum];  // mat mult  (1,row)*(row,col)=(1,col)
    }
    G1 comm=perdersen_commit(g,res,colnum);
    ret=res;
    return comm;
}
G1 gen_gi(G1* g,int n)
{
    const char *g1Str = "1 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
    G1 base;
    base.setStr(g1Str);
    for(int i=0;i<n;i++)
    {
        Fr tmp;
        tmp.setByCSPRNG();
        g[i]=base*tmp;
    }
    return base;
}


Pack bullet_reduce(G1 gamma, Fr*a,G1*g,int n,G1& G,Fr* x,Fr y,bool need_free) // length n
{
    if(n==1)
    {
        Pack p(gamma,a[0],g[0],x[0],y);
        return p;
    }
    timer P(true),V;
    P.start();
    //step2  prover fold
    G1 gamma_minus1,gamma_1;
    Fr x1a2=0,x2a1=0;
    for(int i=0;i<n/2;i++)
    {
        x1a2+=x[i]*a[n/2+i];
        x2a1+=x[n/2+i]*a[i];
    }
    gamma_minus1=G*x1a2+perdersen_commit(g+n/2,x,n/2);
    gamma_1=G*x2a1+perdersen_commit(g,x+n/2,n/2);
    Fr c,invc;
    c.setByCSPRNG();  // step3 V choose random c
    Fr::inv(invc,c);
    P.stop("Bullet proof Part1 fold x dot a",false);
    //prover verifier both comp
    V.start();
    G1 gamma_prime=gamma_minus1*c*c+gamma_1*invc*invc+gamma;
    Fr* aprime=new Fr[n/2];       
    for(int i=0;i<n/2;i++)
        aprime[i]=a[i]*invc+a[i+n/2]*c;
    G1* gprime=new G1[n/2];           
    for(int i=0;i<n/2;i++)
        gprime[i]=g[i]*invc+g[i+n/2]*c;
    V.stop("Verifier ");
    P.stop("Bullet proof Part2 fold a & g",false);
    //prover single compute
    Fr* xprime=new Fr[n/2];         
    Fr yprime;
    for(int i=0;i<n/2;i++)
        xprime[i]=c*x[i]+invc*x[i+n/2];
    yprime=c*c*x1a2+invc*invc*x2a1+y;
    P.stop("Bullet proof Part3 fold x & y",false);
    if(need_free)
    {
        delete []a;
        delete []g;
        delete []x;
    }
    P.stop("Prover Total");
    return bullet_reduce(gamma_prime,aprime,gprime,n/2,G,xprime,yprime,true);
}   

bool prove_dot_product(G1 comm_x, G1 comm_y, Fr* a, G1*g ,G1& G,Fr* x,Fr y,int n)  // y= <a,x> , 
{
    G1 gamma=comm_x+comm_y;
    Pack p=bullet_reduce(gamma,a,g,n,G,x,y);
    assert(p.y==p.x*p.a);
    assert(p.gamma==p.g*p.x+G*p.y);
    cout<<"Hyrax: All check passed!!!"<<endl;
    return true;
}
ThreadSafeQueue<int> workerq,endq;

G1* prover_commit(Fr* w, G1* g, int l,int thread_n) //compute Tk
{
    //w has 2^l length
    cerr<<"call traditional slow commit"<<endl;
    //assert(l%2==0);
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    G1 *Tk=new G1[rownum];
    Fr* row=new Fr[1<<l];
    timer t;
    t.start();
    G1 *W=new G1[COMM_OPT_MAX*thread_n];
    memset(W,0,sizeof(G1)*COMM_OPT_MAX*thread_n);
    for(int i=0;i<rownum;i++) // enumerate row of T  
    {
        for(int j=0;j<colnum;j++)// enum col
            row[i*colnum+j]=w[i+j*rownum];
    }
    for(int i=0;i<rownum;i++) // enumerate row of T  
        Tk[i]=perdersen_commit(g,row+i*colnum,colnum); // each thread use a different W
    t.stop("commit time ");
    delete []W;
    delete []row;
    return Tk;
}
void int_commit_worker(G1*& Tk,G1*& g, ll*& row,int colnum,G1*& W)
{
    int idx;
    while (true)
    {
            bool ret=workerq.TryPop(idx);
            if(ret==false)
                return;
            Tk[idx]=perdersen_commit(g,row+idx*colnum,colnum,W);
            endq.Push(idx);
    }
}
G1* prover_commit(ll* w, G1* g, int l,int thread_n) //compute Tk, int version with pippenger
{
    cerr<<"dog "<<thread_n<<endl;
    //w has 2^l length
    //assert(l%2==0);
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    G1 *Tk=new G1[rownum];
    ll* row=new ll[1<<l];
    timer t;
    t.start();
    G1** W=new G1*[thread_n];
    for(int i=0;i<thread_n;i++)
        W[i]=new G1[COMM_OPT_MAX*block_num];
    for(int i=0;i<thread_n;i++)
        memset(W[i],0,sizeof(G1)*COMM_OPT_MAX*block_num);
    for(int i=0;i<rownum;i++) // enumerate row of T  
    {
        for(int j=0;j<colnum;j++)// enum col
            row[i*colnum+j]=w[i+j*rownum];
    }
    for (u64 i = 0; i < rownum; ++i)  //work for rownum 
        workerq.Push(i);
    for(int i=0;i<thread_n;i++)
    {
        //    Tk[i]=perdersen_commit(g,row+i*colnum,colnum,W); // each thread use a different W
        thread t(int_commit_worker,std::ref(Tk),std::ref(g),std::ref(row),colnum,std::ref(W[i])); 
        t.detach();
    }
    while(!workerq.Empty())
        this_thread::sleep_for (std::chrono::microseconds(10));
    while(endq.Size()!=rownum)
        this_thread::sleep_for (std::chrono::microseconds(10));
    endq.Clear();
    assert(endq.Size()==0);
    t.stop("commit time(PPG) ");
    for(int i=0;i<thread_n;i++)
        delete [] W[i];
    delete []W;

    delete []row;
    return Tk;
}

Fr prover_evaluate(Fr*w ,Fr*r,G1& G,G1* g, Fr*L,Fr*R,int l)  // nlogn brute force 
{
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    timer t(true);
    t.start();
    brute_force_compute_LR(L,R,r,l);
    t.stop("brute force LR ",false);
    Fr eval=brute_force_compute_eval(w,r,l);
    t.stop("eval ",false);
    t.stop("eval total ",true,false);
    return eval;
}
namespace hyrax
{
void verify(Fr*w,Fr*r,Fr eval,G1&G,G1*g,Fr*L,Fr*R,G1*tk,int l)
{
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    Fr* LT=new Fr[colnum];
    timer t;
    t.start();
    compute_LT(w,L,l,g,LT);
    t.stop("prover compute LT ",false);
    G1 tprime=compute_Tprime(w,r,l,g,L,tk);
    t.stop("merge Tprime ",false);
    prove_dot_product(tprime, G*eval, R, g , G,LT,eval,colnum);
}
}