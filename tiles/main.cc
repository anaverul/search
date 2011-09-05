#include "mdist.hpp"
#include "../search/idastar.hpp"
#include "../search/astar.hpp"
#include "../incl/utils.hpp"
#include <cstdio>

static void search(TilesMdist &, Search<TilesMdist> &, TilesMdist::State &);

int main(int argc, char *argv[]) {
	TilesMdist d(stdin);
//	Idastar<TilesMdist, true, true> srch;
	Astar<TilesMdist, true> srch;
	TilesMdist::State s0 = d.initstate();
	search(d, srch, s0);
	return 0;
}

static void search(TilesMdist &d, Search<TilesMdist> &srch, TilesMdist::State &s0) {
	dfheader(stdout);
	Result<TilesMdist> res = srch.search(d, s0);
	dfpair(stdout, "initial heuristic", "%d", d.h(s0));
	res.output(stdout);
	dffooter(stdout);
}

