from typing import Optional

from z3 import *


class DAG:

    def __init__(self):
        self.graph = {}  # node / eq_class -> set of edges
        self.eq = {}  # node -> eq_class
        self.history = []
        self.eq_idx = 0

    # node1->node2
    def add_edge(self, node1, node2):

        # Track nodes if they are new
        if node1 not in self.eq.keys():
            self.graph[node1] = {(node1, node2)}
            self.eq[node1] = None
        if node2 not in self.eq.keys():
            self.graph[node2] = set()
            self.eq[node2] = None

        # Conflict, that is a a circle completed by this edge
        conf = self.check_conflict(node2, node1, "edge")

        # Add edge, possibly to an eq_class type node
        if self.eq[node1] == None:
            self.graph[node1] |= {(node1, node2)}
        else:
            self.graph[f"eq_{self.eq[node1]}"] |= {(node1, node2)}

        return conf

    def eq_nodes(self, node1, node2):

        # Conflict, that is a a circle completed by this equality
        conf = self.check_conflict(node1, node2, "eq")
        if conf is None:
            conf = self.check_conflict(node2, node1, "eq")

        # Merge nodes into eq_class-es, handling the possibility that they are already eq_class-es
        if self.eq[node1] is not None and self.eq[node2] is not None:
            val1 = self.eq[node1]
            val2 = self.eq[node2]
            self.graph[f"eq_{val1}"] |= self.graph[f"eq_{val2}"]
            del self.graph[f"eq_{val2}"]
            for key, value in self.eq.items():
                if value == val2:
                    self.eq[key] = val1
        elif self.eq[node1] is not None:
            val = self.eq[node1]
            self.graph[f"eq_{val}"] |= self.graph[node2]
            del self.graph[node2]
            self.eq[node2] = val
        elif self.eq[node2] is not None:
            val = self.eq[node2]
            self.graph[f"eq_{val}"] |= self.graph[node1]
            del self.graph[node1]
            self.eq[node1] = val
        else:
            val = self.eq_idx
            self.eq_idx += 1
            self.graph[f"eq_{val}"] = self.graph[node1] | self.graph[node2]
            self.eq[f"eq_{val}"] = val
            del self.graph[node1]
            del self.graph[node2]
            self.eq[node1] = val
            self.eq[node2] = val

        return conf

    def check_conflict(self, start, dest, type):
        # Reachability test with BFS
        reachable = []  # aka visited nodes
        investigate = [start]
        parent = {}  # to_node -> (from_node, "edge"/"eq") aka the way we got there
        while len(investigate) != 0:
            curr_node = investigate.pop(-1)

            # If reached, that is a conflict
            if curr_node == dest:
                edges = []
                eqs = []
                p = dest
                c = dest
                while p != start:
                    p, state = parent[p]
                    if state == "edge":
                        edges.append((p, c))
                    else:
                        eqs.append((p, c))
                    c = p
                if type == "edge":
                    edges.append((dest, start))
                else:
                    eqs.append((dest, start))

                return edges, eqs

            # Otherwise the next neighbors are the ones in the same eq_class...
            eq_val = self.eq[curr_node]
            if eq_val is not None:
                for n, v in self.eq.items():
                    if v == eq_val and n not in reachable:
                        reachable.append(n)
                        investigate.append(n)
                        parent[n] = (curr_node, "eq")
                out_edges = self.graph[f"eq_{eq_val}"]
            else:
                out_edges = self.graph[curr_node]

            # ...and the ones connected by an edge
            for e in out_edges:
                n_s, n_d = e
                if n_d not in reachable:
                    reachable.append(n_d)
                    investigate.append(n_d)
                    parent[n_d] = (n_s, "edge")

        return None


class Digraph:

    def __init__(self):
        self.node_pair2edge = {}
        self.edge2node_pair = {}
        self.dag = DAG()

    # Id corresponding to an edge. It MAY tun out to be a positive or a negative.
    # node_1 or node_2 may already exist in the graph, but not necessarily.
    def add_edge(self, edge_id, node_id1, node_id2):
        self.node_pair2edge[(node_id1, node_id2)] = edge_id
        self.edge2node_pair[edge_id] = (node_id1, node_id2)

    # Fixing an 'a->b' edge
    # Returns a conflict if 'b-->a' route already exists
    # Returns the conflict circle
    # That is deps (list of ids corresponding to node-pairs=edges
    # and eqs (list of pairs of ids corresponding to equal nodes)
    def fix_edge(self, id, value) -> Optional[tuple[list, list[tuple]]]:
        if value:  # This structure only tracks positive edges
            node_id1, node_id2 = self.edge2node_pair[id]
            return self.convert_output(self.dag.add_edge(node_id1, node_id2))
        return None

    # Marking two nodes 'a' and 'b' as equal
    # Returns a conflict if 'b-->a' route or 'a-->b' route already exists
    # Returns the conflict circle
    # That is deps (list of ids corresponding to node-pairs=edges
    # and eqs (list of pairs of ids corresponding to equal nodes)
    def eq_node(self, id1, id2) -> Optional[tuple[list, list[tuple]]]:
        return self.convert_output(self.dag.eq_nodes(id1, id2))

    # Convert between node-pair representation and edge representation
    def convert_output(self, output):
        if output is None:
            return None
        edges, eqs = output
        return [self.node_pair2edge[edge] for edge in edges], eqs

    # Clones whole structure for checkpointing
    def clone(self) -> 'Digraph':
        return copy.deepcopy(self)


########################################################################################################################


class UserPropagate(UserPropagateBase):
    def __init__(self, s, relation):
        super(self.__class__, self).__init__(s)

        # Track stack
        self.lim = []  # Trail endpoints for each push
        self.trail = []  # Undo for each fix

        # Track terms, bindings, etc.
        self.id2term = {}  # Note we must use ids as terms have ugly __eq__ overrides
        self.term2value = {}
        self.term_eqs = set()

        # Custom state (auxiliary data structures)
        self.relation = relation
        self.digraph = Digraph()

        # Register callbacks
        self.add_created(self._created)
        self.add_fixed(self._fix)
        self.add_final(self._final)
        self.add_eq(self._eq)

        # TODO fresh

    def _created(self, term):
        # Only register terms which we actually need
        # Also, add to digraph
        if term.decl().eq(self.relation):  # Only edges (nodes are added too on-demand)
            self.add(term)
            self.add(term.arg(0))
            self.add(term.arg(1))
            edge_id = term.get_id()
            node_id1 = term.arg(0).get_id()
            node_id2 = term.arg(1).get_id()

            self.digraph.add_edge(edge_id, node_id1, term.arg(1).get_id())

            print('Created:', term)
            self.id2term[edge_id] = term
            self.id2term[node_id1] = term.arg(0)
            self.id2term[node_id2] = term.arg(1)

    # Standard push-pop
    def push(self):
        print('Push')

        self.lim.append(len(self.trail))

        # Add checkpoint to trail
        # NOTE Do this only 'after' lim appending, because we want to undo the checkpoint too
        old_digraph = self.digraph

        def undo():
            self.digraph = old_digraph

        self.trail.append(undo)
        self.digraph = self.digraph.clone()

    # Standard push-pop
    def pop(self, num_scopes):
        print('Pop')
        # num_scopes = number of pushes to undo
        lim_point = len(self.lim) - num_scopes
        trail_point = self.lim[lim_point]
        while len(self.trail) > trail_point:
            undo_fn = self.trail.pop()
            undo_fn()
        self.lim = self.lim[0:lim_point]

    def _fix(self, term, value):
        print('Fix:', term, " = ", value)
        # term = term to assign
        # value = value to assign, always boolean or bitvector

        # Track in digraph
        conflict = self.digraph.fix_edge(term.get_id(), value)

        # Double-book for debugging purposes
        def undo():
            del self.term2value[term]

        self.trail.append(undo)
        self.term2value[term] = value

        # Report conflicts, possibly regarding this very change. May be delayed until final call though.
        if conflict is not None:
            normalized = self.normalize_conflict(conflict)
            self.print_conflict(normalized)
            # Deps are any term that is fixed, eqs are pairs of terms that are equal
            self.conflict(
                deps=normalized[0],
                eqs=normalized[1],
            )

    def _eq(self, term1, term2):
        print('Eq:', term1, " = ", term2)

        # Track in digraph
        conflict = self.digraph.eq_node(term1.get_id(), term2.get_id())

        # Double-book for debugging purposes
        def undo():
            self.term_eqs.remove((term1, term2))

        self.trail.append(undo)
        self.term_eqs.add((term1, term2))

        # Report conflicts, possibly regarding this very change. May be delayed until final call though.
        if conflict is not None:
            normalized = self.normalize_conflict(conflict)
            self.print_conflict(normalized)
            # Deps are any term that is fixed, eqs are pairs of terms that are equal
            self.conflict(
                deps=normalized[0],
                eqs=normalized[1],
            )

    def _final(self):
        print('Final:', self.term2value, sep='\n')

        # Only testing purpose
        # Nothing to do here

    # Convert ids to terms in a conflict
    def normalize_conflict(self, conflict):
        return [self.id2term[c] for c in conflict[0]], [(self.id2term[c1], self.id2term[c2]) for c1, c2 in conflict[1]]

    def print_conflict(self, conflict):
        print('Conflict:')
        for c in conflict[0]:
            print('-', c, '=', self.term2value[c])
        for c1, c2 in conflict[1]:
            print('-', c1, '==', c2)


# How to use:

NodeSort, N = EnumSort('NodeSort', ['N0', 'N1', 'N2', 'N3'])
# N0, N1, N2, N3 = N

# 1. Create a relation with PropagateFunction. Only such term will be 'created' in any single UserPropagator.
relation = PropagateFunction("R", NodeSort, NodeSort, BoolSort())

# 2. Create variables
# We use functions here, which are basically variables such that
# they come from the NodeSort set,
# so we can express the relation on them,
# and also equalities (because we don't know which is which)
X = Bool('X')
F0 = Function('F0', (BoolSort()), NodeSort)
F1 = Function('F1', (BoolSort()), NodeSort)
F2 = Function('F2', (BoolSort()), NodeSort)
F3 = Function('F3', (BoolSort()), NodeSort)

# 3. Create solver
s = SimpleSolver()

# 4. Create assertions
# Any knowledge regarding the relation is useful,
# negative edges are not directly tracked by the UserPropagator,
# as they never cause conflicts.
# However, the base solver may still need to know them.
known_pos_edges = [
    (F0(X), F1(X)),
    (F1(X), F2(X)),
    (F3(X), F0(X)),
]
known_neg_edges = []
for a, b in known_pos_edges:
    s.add(relation(a, b))
for a, b in known_neg_edges:
    s.add(Not(relation(a, b)))
s.add(Or(F3(X) == F2(X), F3(X) == F1(X)))

# 5. Create one propagator per relation
p = UserPropagate(s, relation=relation)

# 6. Run the solver
result = s.check()
print(result)
if result == 'sat':
    print(s.model())
