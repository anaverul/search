// Copyright © 2013 the Search Authors under the MIT license. See AUTHORS for the list of authors.
#include "../search/search.hpp"
#include "../utils/pool.hpp"
#include <limits>

void fatal(const char*, ...);	// utils.hpp

template <class D> struct Rwastar : public SearchAlgorithm<D> {

	typedef typename D::State State;
	typedef typename D::PackedState PackedState;
	typedef typename D::Cost Cost;
	typedef typename D::Oper Oper;

	struct Node {
		ClosedEntry<Node, D> closedent;
		ClosedEntry<Node, D> seenent;
		int openind;
		Node *parent;
		PackedState state;
		Oper op, pop;
		Cost f, g;
		double fprime;

		Node() : openind(-1) {
		}

		static ClosedEntry<Node, D> &closedentry(Node *n) {
			return n->closedent;
		}

		static PackedState &key(Node *n) {
			return n->state;
		}

		static void setind(Node *n, int i) {
			n->openind = i;
		}

		static int getind(const Node *n) {
			return n->openind;
		}
	
		static bool pred(Node *a, Node *b) {
			if (a->fprime == b->fprime) {
				if (a->f == b->f)
					return a->g > b->g;
				return a->f < b->f;
			}
			return a->fprime < b->fprime;
		}	
	};

	struct Seen{
		static ClosedEntry<Node, D> &closedentry(Node *n) {
			return n->seenent;
		}
		static PackedState &key(Node *n) {
			return n->state;
		}
	};

	Rwastar(int argc, const char *argv[]) :
			SearchAlgorithm<D>(argc, argv), dropdups(false),
			wt(-1.0), closed(30000001), seen(30000001)  {
			w_ind = 0;
			wt=weights[w_ind];
			for (int i = 0; i < argc; i++) {
				if (strcmp(argv[i], "-dropdups") == 0)
					dropdups = true;
			}
			nodes = new Pool<Node>();
	}

	~Rwastar() {
		delete nodes;
	}
	void search(D &d, typename D::State &s0) {
		bool failed = false;
		bound = std::numeric_limits<double>::infinity(); //bound is positive infinity, cause we don't have one
		seen.init(d);
		closed.init(d);
		this->start(); //initialize search?
		dfrowhdr(stdout, "incumbent", 6, "num", "nodes expanded",
			"nodes generated", "weight", "solution cost",
			"wall time");
		while (!SearchAlgorithm<D>::limit() && !failed) { //run out of weights and haven't found a solution = failed
			Node *n0 = init(d, s0);
			closed.prstats(stdout, "");
			closed.clear();
			open.clear();
			closed.prstats(stdout, "");
			open.push(n0);
			closed.add(n0);
			while (!open.empty() && !SearchAlgorithm<D>::limit()) {
				Node *n = *open.pop();
				//if n's f value is greater or equal than my bound, then don't use this node (continue)
				if (n->f >= bound){ //assumes heuristic is admissible
					continue;
				} 
				State buf, &state = d.unpack(buf, n->state);
				bool goal_found = expand(d, n, state);
				if (goal_found){
					goal_count++;
					bound = cand->g;
					dfrow(stdout, "incumbent", "uuuggg", goal_count, this->res.expd,
						this->res.gend, wt, bound,
						walltime() - this->res.wallstart);
					nextwt(); 
					break;
				}
			}
		}
		if(cand) {
			solpath<D, Node>(d, cand, this->res);
		}		
		this->finish(); //report solution
	}
	virtual void reset() {
		SearchAlgorithm<D>::reset();
		open.clear();
		closed.clear();
		seen.clear();
		delete nodes;
		nodes = new Pool<Node>();
	}

	virtual void output(FILE *out) {
		SearchAlgorithm<D>::output(out);
		closed.prstats(stdout, "closed ");
		dfpair(stdout, "open list type", "%s", "binary heap");
		dfpair(stdout, "node size", "%u", sizeof(Node));
		dfpair(stdout, "weight", "%lg", wt); //weight schedule instead of just the weight

	}

private:

	void nextwt() {
		w_ind++;
		if(w_ind < num_weights) {
			wt = weights[w_ind];
		} else {
			wt = 1.0;
		}
	}

	bool expand(D &d, Node *n, State &state) {
		//increases count of expanded nodes and gets all the available operators for the current state i am trying to expand
		//for each of these operators it creates a new child
		//probably do not need to change
		SearchAlgorithm<D>::res.expd++;

		typename D::Operators ops(d, state);
		for (unsigned int i = 0; i < ops.size(); i++) {
			if (ops[i] == n->pop)
				continue;
			SearchAlgorithm<D>::res.gend++;
			if (considerkid(d, n, state, ops[i])){
				return true;
			}
		}
		return false; //if it loops through all the children and none of them are goals
	}

	bool considerkid(D &d, Node *parent, State &state, Oper op) {
		Node *kid = nodes->construct();
		typename D::Edge e(d, state, op);
		kid->g = parent->g + e.cost;
		d.pack(kid->state, e.state); 

		if (d.isgoal(state)){

			if (!cand || kid->g < cand->g) { //check if the g value is worse than the bound
			cand = kid;
			}
		return true;
		}

		unsigned long hash = kid->state.hash(&d);
		Node *dup = static_cast<Node*>(closed.find(kid->state, hash));
		Node *seen_dup = static_cast<Node*>(seen.find(kid->state, hash));
		if (dup) {   // state was in closed
			this->res.dups++;
			if (dropdups || kid->g >= dup->g) { //this would not be in seen_dup
				nodes->destruct(kid);
				return false;
			}
			if (dup->openind < 0)  //if it is already in the open list
				this->res.reopnd++;
			dup->fprime = dup->fprime - dup->g + kid->g;
			dup->f = dup->f - dup->g + kid->g;
			dup->g = kid->g;
			dup->parent = parent;
			dup->op = op;
			dup->pop = e.revop;
			open.pushupdate(dup, dup->openind);
			nodes->destruct(kid);
		} else if (seen_dup) { // state was in seen
			this->res.dups++;
			if (kid->g < seen_dup->g){
				seen_dup->fprime = seen_dup->fprime - seen_dup->g + kid->g;
				seen_dup->f = seen_dup->f - seen_dup->g + kid->g;
				seen_dup->g = kid->g;
				seen_dup->parent = parent;
				seen_dup->op = op;
				seen_dup->pop = e.revop;
			}
			open.push(seen_dup);
			closed.add(seen_dup, hash);
			nodes->destruct(kid);
		} else {
			typename D::Cost h = d.h(e.state);
			kid->f = kid->g + h;
			kid->fprime = kid->g + wt * h;
			kid->parent = parent;
			kid->op = op;
			kid->pop = e.revop;
			closed.add(kid, hash);
			seen.add(kid, hash);
			open.push(kid);
		}
		return false;
	}

	Node *init(D &d, State &s0) {
		Node *n0 = nodes->construct();
		d.pack(n0->state, s0);
		n0->g = Cost(0);
		typename D::Cost h = d.h(s0);
		n0->f = h;
		n0->fprime = wt * h;
		n0->op = n0->pop = D::Nop;
		n0->parent = NULL;
		return n0;
	}

	bool dropdups;
	double wt;
    int num_weights = 5;
    double weights[5] = {5, 3, 2, 1.5, 1};
	double bound;
	int w_ind;
	int goal_count = 0;
	Node *cand; 
	BinHeap<Node, Node*> open;
 	ClosedList<Node, Node, D> closed;
	ClosedList<Seen, Node, D> seen;
	Pool<Node> *nodes;
};
