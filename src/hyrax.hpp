#pragma once
#include <iostream>
#include <vector>
#include <mcl/bls12_381.hpp>
#include "timer.hpp"
using namespace std;
using namespace mcl::bn;

struct Hyrax_proof
{
    //transmitted data
    G1 tprime, comm_w;
    //public data
    G1 *g, G;
    Fr* R;
    //prover only data
    Fr* LT;
    Fr eval;

};
struct Pack 
{
    G1 gamma;
    Fr a;
    G1 g;
    Fr y;
    Fr x;
    Pack(G1 gamm,Fr fa, G1 gg,Fr xx,Fr yy)
    {
        gamma=gamm;
        a=fa;
        g=gg;
        x=xx;
        y=yy;
    }
};
G1 perdersen_commit(G1* g,Fr* f,int n);
Fr lagrange(Fr *r,int l,int k);
void brute_force_compute_LR(Fr* L,Fr* R,Fr* r,int l);
Fr brute_force_compute_eval(Fr* w,Fr* r,int l);
G1 compute_Tprime(Fr* w,Fr* r,int l,G1* g,Fr* L);
G1 compute_LT(Fr*w ,Fr*L,int l,G1*g,Fr*& ret);
G1 gen_gi(G1* g,int n);
Pack bullet_reduce(G1 gamma, Fr*a,G1*g,int n,G1& G,Fr* x,Fr y,bool need_free=false);
bool prove_dot_product(G1 comm_x, G1 comm_y, Fr* a, G1*g ,G1& G,Fr* x,Fr y,int n);
Hyrax_proof prover_commit(Fr* w, Fr* r, G1& G,G1* g, Fr*L,Fr*R,int l);