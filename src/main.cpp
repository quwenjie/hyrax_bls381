//
// Created by juzix on 2021/6/17.
//
#define DEBUG
#include <mcl/bls12_381.hpp>
#include <iostream>
#include "hyrax.hpp"
using namespace std;

using namespace mcl::bn;


const int MAXL=26;
Fr w[(1<<MAXL)],r[MAXL],L[1<<(MAXL/2)],R[1<<(MAXL/2)];
G1 g[1<<(MAXL/2)];

int main(int argc, char *argv[])
{
    initPairing(mcl::BLS12_381);
    int l=24;
    for(int i=0;i<(1<<l);i++)
        w[i]=rand()%65535-30000;

    for(int i=0;i<l;i++)
        r[i].setByCSPRNG();
    G1 G=gen_gi(g,1<<(l/2));
    timer t;
    t.start();
    Hyrax_proof proof=prover_commit(w,r,G,g,L,R,l);
    prove_dot_product(proof.tprime,proof.comm_w,proof.R,proof.g,proof.G,proof.LT,proof.eval,(1<<(l/2)));  // tprime, comm_w ,R,g,G public, LT eval only prover knows
    t.stop("All time: ");
    return 0;
}
