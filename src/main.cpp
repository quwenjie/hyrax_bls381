//
// Created by juzix on 2021/6/17.
//
#undef NDEBUG
#include <mcl/bls12_381.hpp>
#include <iostream>
#include "hyrax.hpp"
using namespace std;

using namespace mcl::bn;
using namespace hyrax;

const int MAXL=26;
ll ww[(1<<MAXL)];
Fr w[(1<<MAXL)];
Fr r[MAXL],L[1<<(MAXL/2)],R[1<<(MAXL/2)];
G1 g[1<<(MAXL/2)];
void field(const char* f,Fr x)
{
    if(x.isNegative())
        cout<<f<<" -"<<-x<<endl;
    else
        cout<<f<<" "<<x<<endl;
    
}
int main(int argc, char *argv[])
{
    initPairing(mcl::BLS12_381);
    Fr x(-9),y(14);
    cout<<x<<" "<<y<<endl;
    int l=23;
    for(int i=0;i<(1<<l)-100;i++)
    {
        ww[i]=1ll*(rand()%2000-1000);
        w[i]=ww[i];
    }
    for(int i=(1<<l)-50000;i<(1<<l);i++)
    {
        if(i&1)
            ww[i]=1ll<<63;
        else    
            ww[i]=(1ll<<63)-i;
        w[i]=ww[i];
    }
    //cout<<(ww[(1<<l)-40000]>(((ll)1)<<66))<<endl;
    //cout<<(ww[(1<<l)-40000]>(((ll)1)<<64))<<endl;
    //cout<<(ww[(1<<l)-40000]>(((ll)1)<<68))<<endl;
    /*Fr a0=Fr(ww[(1<<l)-40000]*4);
    Fr a1=Fr(ww[(1<<l)-40000]);
    Fr a2=Fr(((ll)1)<<66);
    Fr a3=Fr(((ll)1)<<64);
    cout<<a1<<" "<<a1-ww[(1<<l)-40000]<<endl;;
    */
   
    for(int i=0;i<l;i++)
        r[i].setByCSPRNG();
    G1 G=gen_gi(g,1<<(l/2));
    timer t;
    t.start();
    G1*tk=prover_commit(ww,g,l,16);  //77s, ppg: 
    cout<<w[(1<<l)-40000]<<endl;
    field("ATC ",w[(1<<l)-40000]);
    cerr<<"end here"<<endl;
    //w[0]+=1;
    Fr eva=prover_evaluate(w,r,G,g,L,R,l);
    hyrax::verify(w,r,eva,G,g,L,R,tk,l);  // tprime, comm_w ,R,g,G public, LT eval only prover knows
    t.stop("All time: ");
    return 0;
}


//TODO: long long 1x slower than int, should optimize