import cProfile
import queue

import random
from typing import Optional
import time

from z3 import *

debug = False


def nothing(*args, **kwargs):
    pass


debug_print = print if debug else nothing
should_profile = False


class DAG:

    def __init__(self, check_on_single):
        self.check_on_single = check_on_single
        self.graph = {}  # node / eq_class -> set of edges
        self.eq = {}  # node -> eq_class
        self.history = []
        self.eq_idx = 0

    # node1->node2
    def fix_edge(self, node1, node2):
        # Track nodes if they are new
        if node1 not in self.eq.keys():
            self.graph[node1] = {(node1, node2)}
            self.eq[node1] = None
        if node2 not in self.eq.keys():
            self.graph[node2] = set()
            self.eq[node2] = None

        # Conflict, that is a circle completed by this edge
        conf = self.check_conflict_single(node2, node1, "edge")

        # Add edge, possibly to an eq_class type node
        if self.eq[node1] == None:
            self.graph[node1] |= {(node1, node2)}
        else:
            self.graph[f"eq_{self.eq[node1]}"] |= {(node1, node2)}

        return conf

    def eq_nodes(self, node1, node2):

        # Conflict, that is a a circle completed by this equality
        conf = self.check_conflict_single(node1, node2, "eq")
        if conf is None:
            conf = self.check_conflict_single(node2, node1, "eq")

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

    def check_conflict_single(self, start, dest, type):
        if not self.check_on_single:
            return None
        # Reachability test with BFS
        reachable = set()  # aka visited nodes
        investigate = queue.Queue()
        investigate.put(start)
        parent = {}  # to_node -> (from_node, "edge"/"eq") aka the way we got there
        while not investigate.empty():
            curr_node = investigate.get()

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
                        reachable.add(n)
                        investigate.put(n)
                        parent[n] = (curr_node, "eq")
                out_edges = self.graph[f"eq_{eq_val}"]
            else:
                out_edges = self.graph[curr_node]

            # ...and the ones connected by an edge
            for e in out_edges:
                n_s, n_d = e
                if n_d not in reachable:
                    reachable.add(n_d)
                    investigate.put(n_d)
                    parent[n_d] = (n_s, "edge")

        return None

    def check_conflict_global(self):
        # Count the inedges for the nodes
        in_counts = {}
        for key in self.graph.keys():
            in_counts[key] = 0
        for values in self.graph.values():
            for edge in values:
                n1, n2 = edge
                if self.eq[n2] is not None:
                    in_counts[f"eq_{self.eq[n2]}"] += 1
                else:
                    in_counts[n2] += 1

        nodes = set(self.graph.keys())  # remaining nodes

        # Whil remaining nodes, find a node with no inedges
        while len(nodes) != 0:
            zeronode = None
            for node in nodes:
                if in_counts[node] == 0:
                    zeronode = node
                    break

            # If there is no such node, there is a cycle
            if zeronode is None:

                # Create a 'subgraph'...
                children = {}
                for node in nodes:
                    children[node] = set()
                    for edge in self.graph[node]:
                        n1, n2 = edge
                        if self.eq[n2] is not None:
                            n2 = f"eq_{self.eq[n2]}"
                        if n2 in nodes:
                            children[node].add(n2)
                # ... by removing all nodes that are not in a cycle
                change = True
                while change:
                    change = False
                    nodes_to_remove = set()
                    for node in nodes:
                        if len(children[node]) == 0:
                            change = True
                            nodes_to_remove.add(node)
                    for node in children.keys():
                        children[node] -= nodes_to_remove
                    for node in nodes_to_remove:
                        del children[node]
                        nodes.remove(node)

                # Eah remaining node is in a cycle
                # We traverse on of them
                curr_node = next(iter(nodes))
                nodes_travelled = []
                edges_travelled = []
                while curr_node not in nodes_travelled:
                    nodes_travelled.append(curr_node)
                    edges = self.graph[curr_node]
                    for edge in edges:
                        n1, n2 = edge
                        if self.eq[n2] is not None:
                            n2 = f"eq_{self.eq[n2]}"
                        if n2 in nodes:
                            curr_node = n2
                            edges_travelled.append(edge)
                            break

                # Since there can be multiple cycles,
                # we only keep the one that contains the circle we are looking for
                idx = nodes_travelled.index(curr_node)
                edges_travelled = edges_travelled[idx:]
                eqs_travelled = []
                for i in range(len(edges_travelled) - 1):
                    edge1 = edges_travelled[i]
                    edge2 = edges_travelled[i + 1]
                    if edge1[1] != edge2[0]:
                        eqs_travelled.append((edge1[1], edge2[0]))
                if edges_travelled[0][0] != edges_travelled[-1][1]:
                    eqs_travelled.append((edges_travelled[0][0], edges_travelled[-1][1]))

                return edges_travelled, eqs_travelled

            # Otherwise, delete the node and update the inedge counts
            nodes.remove(zeronode)
            for edge in self.graph[zeronode]:
                n1, n2 = edge
                if self.eq[n2] is not None:
                    in_counts[f"eq_{self.eq[n2]}"] -= 1
                else:
                    in_counts[n2] -= 1
        return None


class Digraph:

    def __init__(self, check_on_single):
        self.node_pair2edge = {}
        self.edge2node_pair = {}
        self.dag = DAG(check_on_single)

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
            return self.convert_output(self.dag.fix_edge(node_id1, node_id2))
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

    # Checks for any conflict in graph
    def check(self):
        return self.convert_output(self.dag.check_conflict_global())


########################################################################################################################


class UserPropagate(UserPropagateBase):
    def __init__(self, s, relation, check_on_single):
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
        self.digraph = Digraph(check_on_single)

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

            debug_print('Created:', term)
            self.id2term[edge_id] = term
            self.id2term[node_id1] = term.arg(0)
            self.id2term[node_id2] = term.arg(1)

    # Standard push-pop
    def push(self):
        debug_print('Push')

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
        debug_print('Pop')
        # num_scopes = number of pushes to undo
        lim_point = len(self.lim) - num_scopes
        trail_point = self.lim[lim_point]
        while len(self.trail) > trail_point:
            undo_fn = self.trail.pop()
            undo_fn()
        self.lim = self.lim[0:lim_point]

    def _fix(self, term, value):
        debug_print('Fix:', term, " = ", value)
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
        debug_print('Eq:', term1, " = ", term2)

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
        debug_print('Final:', self.term2value, sep='\n')

        # Last chance to report conflicts.
        conflict = self.digraph.check()
        if conflict is not None:
            normalized = self.normalize_conflict(conflict)
            self.print_conflict(normalized)
            # Deps are any term that is fixed, eqs are pairs of terms that are equal
            self.conflict(
                deps=normalized[0],
                eqs=normalized[1],
            )

    # Convert ids to terms in a conflict
    def normalize_conflict(self, conflict):
        return [self.id2term[c] for c in conflict[0]], [(self.id2term[c1], self.id2term[c2]) for c1, c2 in conflict[1]]

    def print_conflict(self, conflict):
        if debug:
            print('Conflict:')
            for c in conflict[0]:
                print('-', c, '=', self.term2value[c])
            for c1, c2 in conflict[1]:
                print('-', c1, '==', c2)


def example():
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
    F0 = Function('F0', NodeSort)
    F1 = Function('F1', NodeSort)
    F2 = Function('F2', NodeSort)
    F3 = Function('F3', NodeSort)

    # 3. Create solver
    s = SimpleSolver()

    # 4. Create assertions
    # Any knowledge regarding the relation is useful,
    # negative edges are not directly tracked by the UserPropagator,
    # as they never cause conflicts.
    # However, the base solver may still need to know them.
    known_pos_edges = [
        (F0, F1),
        (F1, F2),
        (F3, F0),
    ]
    known_neg_edges = []
    for a, b in known_pos_edges:
        s.add(relation(a, b))
    for a, b in known_neg_edges:
        s.add(Not(relation(a, b)))
    s.add(Or(F3 == F2, F3 == F1))

    # 5. Create one propagator per relation
    p = UserPropagate(s, relation=relation)

    # 6. Run the solver
    result = s.check()
    print(result)
    if result == 'sat':
        print(s.model())


########################################################################################################################

class RandomGraph:

    def __init__(self, *, num_nodes, edge_probability, eq_num, relation_name='R'):
        self.relation_name = relation_name
        self.graph = {}
        self.eqs = []
        for i in range(num_nodes):
            neighbours = set()
            for j in range(num_nodes):
                if random.random() < edge_probability:
                    neighbours |= {f"node_{j}"}
            self.graph[f"node_{i}"] = neighbours
        for _ in range(eq_num):
            i, j, k, l = random.sample(range(num_nodes), 4)
            self.eqs.append((f"node_{i}", f"node_{j}", f"node_{k}", f"node_{l}"))

    def as_assertions(self, solver, ctx):
        NodeSort, all_nodes = EnumSort(f'{self.relation_name}_sort', list(self.graph.keys()), ctx=ctx)
        node_mapping = dict(zip(self.graph.keys(), all_nodes))
        R = Function(self.relation_name, NodeSort, NodeSort, BoolSort(ctx=ctx))
        for key in self.graph.keys():
            for value in self.graph[key]:
                solver.add(R(node_mapping[key], node_mapping[value]))
        for node1, node2, node3, node4 in self.eqs:
            solver.add(Or(node_mapping[node1] == node_mapping[node2], node_mapping[node3] == node_mapping[node4]))

        f = Function(f'{self.relation_name}_f', NodeSort, NodeSort, IntSort(ctx=ctx))
        X = Const(f'{self.relation_name}_X', NodeSort)
        Y = Const(f'{self.relation_name}_Y', NodeSort)
        Z = Const(f'{self.relation_name}_Z', NodeSort)
        solver.add(ForAll([X, Y, Z], Implies(And(R(X, Y), R(Y, Z)), f(X, Y) < f(Y, Z))))

    def as_user_propagator(self, solver, ctx):
        NodeSort, all_nodes = EnumSort(f'{self.relation_name}_sort', list(self.graph.keys()), ctx=ctx)
        node_mapping = dict(zip(self.graph.keys(), all_nodes))
        R = PropagateFunction(self.relation_name, NodeSort, NodeSort, BoolSort(ctx=ctx))
        for key in self.graph.keys():
            for value in self.graph[key]:
                solver.add(R(node_mapping[key], node_mapping[value]))
        for node1, node2, node3, node4 in self.eqs:
            solver.add(Or(node_mapping[node1] == node_mapping[node2], node_mapping[node3] == node_mapping[node4]))

        p = UserPropagate(solver, relation=R, check_on_single=False)


def benchmark():
    results = {}
    for num_nodes in [500]:
        for edge_probability in [0.002]:
            for eq_num in [0]:
                for i in range(100):
                    g = RandomGraph(
                        num_nodes=num_nodes,
                        edge_probability=edge_probability,
                        eq_num=eq_num,
                    )
                    for type in 'assertions', 'user_propagator':
                        print(
                            f'{f"num_nodes={num_nodes}, edge_p={edge_probability}, eq_num={eq_num}, i={i}, type={type}":80}',
                            end='\t',
                        )

                        if should_profile:
                            profiler = cProfile.Profile()

                        lengths = []
                        for j in range(3):
                            ctx = Context()
                            s = SimpleSolver(ctx=ctx)
                            if type == 'assertions':
                                g.as_assertions(s, ctx)
                            else:
                                g.as_user_propagator(s, ctx)

                            if should_profile:
                                profiler.enable()
                            start = time.time()
                            result = s.check()
                            end = time.time()
                            if should_profile:
                                profiler.disable()

                            length = end - start
                            lengths.append(length)

                        avg_length = sum(lengths) / len(lengths)
                        print(result, avg_length)

                        if not debug and should_profile:
                            profiler.print_stats(sort='tottime')
                            profiler.print_stats(sort='cumtime')

                        results[(num_nodes, edge_probability, eq_num, i, type)] = (avg_length, result)

                        # save as csv
                        with open('results.csv', 'w') as f:
                            f.write('num_nodes,edge_probability,eq_num,i,type,length,result\n')
                            for key, value in results.items():
                                f.write(','.join(map(str, key + value)) + '\n')

                    if results[(num_nodes, edge_probability, eq_num, i, 'assertions')][1] == results[
                        (num_nodes, edge_probability, eq_num, i, 'user_propagator')][1]:
                        print('same', end='\t')
                    else:
                        print('different', end='\t')
                    if results[(num_nodes, edge_probability, eq_num, i, 'assertions')][0] > results[
                        (num_nodes, edge_probability, eq_num, i, 'user_propagator')][0]:
                        print(':)')
                    else:
                        print(':(')


if __name__ == '__main__':
    benchmark()
