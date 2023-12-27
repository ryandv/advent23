// Advent of Code 2023 Day 25 solution
//
// Using maximum adjacency search to implement Stoer-Wagner algorithm
// and component counting of graphs with constant weight 1
//
// https://www.cs.dartmouth.edu/~ac/Teach/CS105-Winter05/Handouts/stoerwagner-mincut.pdf
// https://dl.acm.org/doi/pdf/10.5555/313559.313872
// https://www.cs.tau.ac.il/~zwick/grad-algo-08/gmc.pdf
// https://www.boost.org/doc/libs/1_83_0/libs/graph/doc/maximum_adjacency_search.html
// https://www.boost.org/doc/libs/1_83_0/boost/graph/stoer_wagner_min_cut.hpp
//
// Test suite including solution should complete on the order of minutes
// on an average desktop under the release cargo profile

use std::collections::BinaryHeap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;

use std::io;
use std::io::prelude::*;

use std::hash::{Hash, Hasher};
use std::ops::FnMut;
use std::rc::Rc;

#[derive(Clone, Debug)]
struct Graph<T: Clone + Eq + Ord + Hash> {
    pub vertices: HashSet<Vertex<T>>,
    pub edges: HashMap<Edge<T>, usize>,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Ord, PartialOrd)]
struct Vertex<T: Clone + Eq + Ord + Hash>(BTreeSet<Rc<T>>);

impl<T: Clone + Eq + Ord + Hash> Vertex<T> {
    pub fn new(t: T) -> Vertex<T> {
        Vertex(BTreeSet::from([Rc::new(t)]))
    }

    pub fn merge(&self, other: &Self) -> Vertex<T> {
        let Vertex(u) = self;
        let Vertex(v) = other;
        Vertex(u | v)
    }
}

impl<T: Clone + Eq + Ord + Hash> IntoIterator for Vertex<T> {
    type Item = Rc<T>;
    type IntoIter = <std::collections::BTreeSet<Rc<T>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Clone, Debug)]
struct Edge<T: Clone + Eq + Ord + Hash>(usize, UnorderedPair<Vertex<T>>);

impl<T: Clone + Eq + Ord + Hash> Edge<T> {
    pub fn new(id: usize, u: Vertex<T>, v: Vertex<T>) -> Edge<T> {
        Edge(id, UnorderedPair((u, v)))
    }

    pub fn partner(&self, v: &Vertex<T>) -> &Vertex<T> {
        self.1.partner(v)
    }

    pub fn joins(&self, v: &Vertex<T>) -> bool {
        self.1.contains(v)
    }

}

impl<T: Clone + Eq + Ord + Hash> PartialEq for Edge<T> {
    fn eq(&self, other: &Self) -> bool {
        self.1.eq(&other.1)
    }
}

impl<T: Clone + Eq + Ord + Hash> Eq for Edge<T> { }

impl<T: Clone + Eq + Ord + Hash> Hash for Edge<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.1.hash(state);
    }
}

impl<T: Clone + Eq + Ord + Hash> Graph<T> {
    pub fn from_adjacency_lists<I: std::iter::IntoIterator<Item = (Edge<T>, usize)>>(adjacency_list: I) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashMap::new(),
        };

        adjacency_list.into_iter().for_each(|(Edge(i, UnorderedPair((u, v))), _w)| {
            g.vertices.insert(u.clone());
            g.vertices.insert(v.clone());
            g.edges.insert(Edge::new(i, u, v), 1);
        });

        g
    }

    fn merge(&self, u: &Vertex<T>, v: &Vertex<T>) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashMap::<Edge<T>, usize>::new(),
        };

        self.vertices.iter().for_each(|x| {
            if x != u && x != v {
                g.vertices.insert(x.clone());
            }
        });
        self.edges.iter().for_each(|(e@Edge(i, UnorderedPair((s, t))), w)| {
            if *e != Edge::new(*i, u.clone(), v.clone()) {
                if e.joins(&u) {
                    let x = e.partner(&u);
                    let w0 = w + self.edges.get(&Edge::new(*i, x.clone(), v.clone())).unwrap_or(&0);
                    g.edges.insert(Edge::new(*i, u.merge(v), x.clone()), w0);
                } else if e.joins(&v) {
                    let x = e.partner(&v);
                    let w0 = w + self.edges.get(&Edge::new(*i, x.clone(), u.clone())).unwrap_or(&0);
                    g.edges.insert(Edge::new(*i, u.merge(v), x.clone()), w0);
                } else {
                    g.edges.insert(Edge::new(*i, s.clone(), t.clone()), *w);
                }
            }
        });
        g.vertices.insert(u.merge(v));

        g
    }

    pub fn maximum_adjacency_search<F>(&self, mut visitor: F, origin: &Vertex<T>) where
        F: FnMut(&Vertex<T>, &HashMap<&Vertex<T>, usize>),
    {
        let mut pq: BinaryHeap<(usize, &Vertex<T>)> = BinaryHeap::new();
        let mut vertices_visited: HashSet<&Vertex<T>> = HashSet::new();
        let mut adjacencies: HashMap<&Vertex<T>, usize> = HashMap::new();
        pq.push((usize::MAX, origin));

        while !pq.is_empty() {
            let (p, v) = pq.pop().unwrap();
            if vertices_visited.contains(v) {
                continue;
            }

            self.edges.iter().filter(|(e, _w)| e.joins(v)).for_each(|(e, w)| {
                let u = e.partner(&v);
                match adjacencies.get(&u) {
                    None => {
                        adjacencies.insert(u, *w);
                        pq.push((*w, u));
                    },
                    Some(w_prev) => {
                        let w_next = w_prev + *w;
                        adjacencies.insert(u, w_next);
                        pq.push((w_next, u));
                    }
                }
            });

            visitor(v, &adjacencies);

            vertices_visited.insert(&v);
        }
    }

    pub fn stoer_wagner(&self, origin: &Vertex<T>) -> HashSet<Edge<T>> {
        let mut g: Graph<T> = self.clone();
        let mut min_cut_weight = usize::MAX;
        let mut inducing_vertex = origin.clone();

        while g.vertices.len() > 1 {
            let mut t = origin.clone();
            let mut s = origin.clone();
            let mut cut_of_the_phase_weight = usize::MAX;

            let visitor = |v: &Vertex<T>, adjacencies: &HashMap<&Vertex<T>, usize>| {
                s = t.clone();
                t = v.clone();
                cut_of_the_phase_weight = *adjacencies.get(v).unwrap_or(&usize::MAX);
            };
            g.maximum_adjacency_search(visitor, origin);

            if cut_of_the_phase_weight < min_cut_weight {
                min_cut_weight = cut_of_the_phase_weight;
                inducing_vertex = t.clone();
            }

            if s == t {
                break;
            }
            g = g.merge(&s, &t);
        }

        HashSet::from_iter(self.edges.iter()
            .filter(|(Edge(_, UnorderedPair((u, v))), _w)| inducing_vertex.0.is_superset(&u.0) ^ inducing_vertex.0.is_superset(&v.0))
            .map(|(e, w)| e.clone()))
    }
}

#[derive(Clone, Debug, PartialOrd, Ord)]
struct UnorderedPair<T: Eq>((T, T));

impl<T: Eq> PartialEq for UnorderedPair<T> {
    fn eq(&self, other: &Self) -> bool {
        let UnorderedPair((s, t)) = self;
        let UnorderedPair((u, v)) = other;

        s == u && t == v || s == v && t == u
    }
}

impl<T: Eq> Eq for UnorderedPair<T> { }

impl<T: Hash + Ord> Hash for UnorderedPair<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let UnorderedPair((s, t)) = self;
        if s <= t {
            s.hash(state);
            t.hash(state);
        } else {
            t.hash(state);
            s.hash(state);
        }
    }
}

impl<T: Eq> UnorderedPair<T> {
    pub fn contains(&self, t: &T) -> bool {
        let UnorderedPair((u, v)) = self;
        *u == *t || *v == *t
    }

    pub fn partner(&self, t: &T) -> &T {
        let UnorderedPair((u, v)) = self;
        if u == t { v } else { u }
    }
}

fn parse_input(input: &str) -> Result<Graph<&str>, &str> {
    input.lines().try_fold(Graph { vertices: HashSet::new(), edges: HashMap::new() }, |mut g, ln| -> Result<Graph<&str>, &str> {
        let mut i = 0;
        let (u, vs) = ln.split_once(": ").ok_or("missing colon delimiter")?;

        g.vertices.insert(Vertex::new(u));
        vs.split(" ").for_each(|v| {
            g.vertices.insert(Vertex::new(v));
            g.edges.insert(Edge::new(i, Vertex::new(u), Vertex::new(v)), 1);
            i += 1;
        });

        Ok(g)
    })
}

fn solve(input: &str) -> Result<usize, &str> {
    let g = parse_input(input)?;
    let origin = g.vertices.iter().next().ok_or("empty graph")?;
    let cut = g.stoer_wagner(origin);
    let mut severed_graph = Graph::from_adjacency_lists(HashSet::<(Edge<&str>, usize)>::from_iter(g.edges.iter().map(|(e, w)| (e.clone(), *w))).difference(&cut.iter().map(|e| (e.clone(), 1)).collect()).map(|x| x.clone()).collect::<HashSet<(Edge<&str>, usize)>>());
    severed_graph.vertices.extend(g.vertices.difference(&severed_graph.vertices.clone()).map(|v| v.clone()));
    let Edge(_, UnorderedPair((s, t))) = cut.iter().next().ok_or("empty cut")?;

    let mut ns = 0;
    let mut nt = 0;
    let svisitor = |v: &Vertex<&str>, adjacencies: &HashMap<&Vertex<&str>, usize>| {
        ns += 1;
    };
    let tvisitor = |v: &Vertex<&str>, adjacencies: &HashMap<&Vertex<&str>, usize>| {
        nt += 1;
    };

    severed_graph.maximum_adjacency_search(svisitor, s);
    severed_graph.maximum_adjacency_search(tvisitor, t);

    println!("{:?} {}\n", ns, nt);

    Ok(ns * nt)
}

fn main() -> io::Result<()> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;

    Ok(())
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
mod test {
    use std::ops::Deref;
    use super::*;

    const TEST_GRAPH_VERTEX_COUNT: usize = 5;

    impl quickcheck::Arbitrary for Graph<usize> {
        fn arbitrary(gen: &mut quickcheck::Gen) -> Graph<usize> {
            let mut id = 0;
            Graph::from_adjacency_lists((0..TEST_GRAPH_VERTEX_COUNT)
                .map(|i| (i, (0..TEST_GRAPH_VERTEX_COUNT).map(|j| i != j && bool::arbitrary(gen)).collect::<Vec<bool>>()))
                .flat_map(|(i, neighbours)| {
                    neighbours
                        .iter()
                        .enumerate()
                        .filter(|adjacency| *adjacency.1)
                        .map(|adjacency| {
                            let e = (Edge::new(i, Vertex::new(i), Vertex::new(adjacency.0)), 1);
                            id += 1;
                            e
                        })
                        .collect::<Vec<(Edge<usize>, usize)>>()
                })
                .collect::<Vec<(Edge<usize>, usize)>>())
        }
    }

    #[derive(Clone, Debug)]
    struct SubsetVector([bool; TEST_GRAPH_VERTEX_COUNT]);

    impl quickcheck::Arbitrary for SubsetVector {
        fn arbitrary(gen: &mut quickcheck::Gen) -> SubsetVector {
            SubsetVector((0..TEST_GRAPH_VERTEX_COUNT).map(|_| bool::arbitrary(gen)).collect::<Vec<bool>>().try_into().unwrap())
        }
    }

    #[test]
    fn parses_example_into_graph() {
        const input: &'static str =
            "jqt: rhn xhk nvd\n\
             rsh: frs pzl lsr\n\
             xhk: hfx\n\
             cmg: qnr nvd lhk bvb\n\
             rhn: xhk bvb hfx\n\
             bvb: xhk hfx\n\
             pzl: lsr hfx nvd\n\
             qnr: nvd\n\
             ntq: jqt hfx bvb xhk\n\
             nvd: lhk\n\
             lsr: lhk\n\
             rzs: qnr cmg lsr rsh\n\
             frs: qnr lhk lsr";
        let expected_vertices = HashSet::from_iter([
            Vertex::new("bvb"),Vertex::new("cmg"),Vertex::new("frs"),Vertex::new("hfx"),
            Vertex::new("jqt"),Vertex::new("lhk"),Vertex::new("lsr"),Vertex::new("ntq"),
            Vertex::new("nvd"),Vertex::new("pzl"),Vertex::new("qnr"),Vertex::new("rhn"),
            Vertex::new("rsh"),Vertex::new("rzs"),Vertex::new("xhk")
        ]);
        let expected_edges = HashMap::from_iter([
            (Edge::new(0, Vertex::new("jqt"), Vertex::new("rhn")), 1),
            (Edge::new(1, Vertex::new("jqt"), Vertex::new("xhk")), 1),
            (Edge::new(2, Vertex::new("jqt"), Vertex::new("nvd")), 1),
            (Edge::new(3, Vertex::new("rsh"), Vertex::new("frs")), 1),
            (Edge::new(4, Vertex::new("rsh"), Vertex::new("pzl")), 1),
            (Edge::new(5, Vertex::new("rsh"), Vertex::new("lsr")), 1),
            (Edge::new(6, Vertex::new("xhk"), Vertex::new("hfx")), 1),
            (Edge::new(7, Vertex::new("cmg"), Vertex::new("qnr")), 1),
            (Edge::new(8, Vertex::new("cmg"), Vertex::new("nvd")), 1),
            (Edge::new(9, Vertex::new("cmg"), Vertex::new("lhk")), 1),
            (Edge::new(10, Vertex::new("cmg"), Vertex::new("bvb")), 1),
            (Edge::new(10, Vertex::new("rhn"), Vertex::new("xhk")), 1),
            (Edge::new(11, Vertex::new("rhn"), Vertex::new("bvb")), 1),
            (Edge::new(12, Vertex::new("rhn"), Vertex::new("hfx")), 1),
            (Edge::new(13, Vertex::new("bvb"), Vertex::new("xhk")), 1),
            (Edge::new(14, Vertex::new("bvb"), Vertex::new("hfx")), 1),
            (Edge::new(15, Vertex::new("pzl"), Vertex::new("lsr")), 1),
            (Edge::new(16, Vertex::new("pzl"), Vertex::new("hfx")), 1),
            (Edge::new(17, Vertex::new("pzl"), Vertex::new("nvd")), 1),
            (Edge::new(18, Vertex::new("qnr"), Vertex::new("nvd")), 1),
            (Edge::new(19, Vertex::new("ntq"), Vertex::new("jqt")), 1),
            (Edge::new(20, Vertex::new("ntq"), Vertex::new("hfx")), 1),
            (Edge::new(21, Vertex::new("ntq"), Vertex::new("bvb")), 1),
            (Edge::new(22, Vertex::new("ntq"), Vertex::new("xhk")), 1),
            (Edge::new(23, Vertex::new("nvd"), Vertex::new("lhk")), 1),
            (Edge::new(24, Vertex::new("lsr"), Vertex::new("lhk")), 1),
            (Edge::new(25, Vertex::new("rzs"), Vertex::new("qnr")), 1),
            (Edge::new(26, Vertex::new("rzs"), Vertex::new("cmg")), 1),
            (Edge::new(27, Vertex::new("rzs"), Vertex::new("lsr")), 1),
            (Edge::new(28, Vertex::new("rzs"), Vertex::new("rsh")), 1),
            (Edge::new(29, Vertex::new("frs"), Vertex::new("qnr")), 1),
            (Edge::new(30, Vertex::new("frs"), Vertex::new("lhk")), 1),
            (Edge::new(31, Vertex::new("frs"), Vertex::new("lsr")), 1),
        ]);

        let g = parse_input(input).unwrap();
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(expected_edges, g.edges);
    }

    #[test]
    fn graphs_constructible_from_adjacency_lists() {
        let adjacency_list: HashMap<Edge<&str>, usize> = HashMap::from_iter([
            (Edge::new(0, Vertex::new("jqt"), Vertex::new("rhn")), 1),
            (Edge::new(1, Vertex::new("jqt"), Vertex::new("xhk")), 1),
            (Edge::new(2, Vertex::new("jqt"), Vertex::new("nvd")), 1),
            (Edge::new(3, Vertex::new("rsh"), Vertex::new("frs")), 1),
            (Edge::new(4, Vertex::new("rsh"), Vertex::new("pzl")), 1),
            (Edge::new(5, Vertex::new("rsh"), Vertex::new("lsr")), 1),
            (Edge::new(6, Vertex::new("xhk"), Vertex::new("hfx")), 1),
            (Edge::new(7, Vertex::new("cmg"), Vertex::new("qnr")), 1),
            (Edge::new(8, Vertex::new("cmg"), Vertex::new("nvd")), 1),
            (Edge::new(9, Vertex::new("cmg"), Vertex::new("lhk")), 1),
            (Edge::new(10, Vertex::new("cmg"), Vertex::new("bvb")), 1),
            (Edge::new(10, Vertex::new("rhn"), Vertex::new("xhk")), 1),
            (Edge::new(11, Vertex::new("rhn"), Vertex::new("bvb")), 1),
            (Edge::new(12, Vertex::new("rhn"), Vertex::new("hfx")), 1),
            (Edge::new(13, Vertex::new("bvb"), Vertex::new("xhk")), 1),
            (Edge::new(14, Vertex::new("bvb"), Vertex::new("hfx")), 1),
            (Edge::new(15, Vertex::new("pzl"), Vertex::new("lsr")), 1),
            (Edge::new(16, Vertex::new("pzl"), Vertex::new("hfx")), 1),
            (Edge::new(17, Vertex::new("pzl"), Vertex::new("nvd")), 1),
            (Edge::new(18, Vertex::new("qnr"), Vertex::new("nvd")), 1),
            (Edge::new(19, Vertex::new("ntq"), Vertex::new("jqt")), 1),
            (Edge::new(20, Vertex::new("ntq"), Vertex::new("hfx")), 1),
            (Edge::new(21, Vertex::new("ntq"), Vertex::new("bvb")), 1),
            (Edge::new(22, Vertex::new("ntq"), Vertex::new("xhk")), 1),
            (Edge::new(23, Vertex::new("nvd"), Vertex::new("lhk")), 1),
            (Edge::new(24, Vertex::new("lsr"), Vertex::new("lhk")), 1),
            (Edge::new(25, Vertex::new("rzs"), Vertex::new("qnr")), 1),
            (Edge::new(26, Vertex::new("rzs"), Vertex::new("cmg")), 1),
            (Edge::new(27, Vertex::new("rzs"), Vertex::new("lsr")), 1),
            (Edge::new(28, Vertex::new("rzs"), Vertex::new("rsh")), 1),
            (Edge::new(29, Vertex::new("frs"), Vertex::new("qnr")), 1),
            (Edge::new(30, Vertex::new("frs"), Vertex::new("lhk")), 1),
            (Edge::new(31, Vertex::new("frs"), Vertex::new("lsr")), 1),
        ]);
        let expected_vertices = HashSet::from_iter([
            Vertex::new("bvb"),Vertex::new("cmg"),Vertex::new("frs"),Vertex::new("hfx"),
            Vertex::new("jqt"),Vertex::new("lhk"),Vertex::new("lsr"),Vertex::new("ntq"),
            Vertex::new("nvd"),Vertex::new("pzl"),Vertex::new("qnr"),Vertex::new("rhn"),
            Vertex::new("rsh"),Vertex::new("rzs"),Vertex::new("xhk")
        ]);

        let g = Graph::from_adjacency_lists(adjacency_list.clone());
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(adjacency_list, g.edges);
    }

    fn most_tightly_connected<T: Clone + Eq + Ord + Hash>(g: &Graph<T>, scanned_vertices: &HashSet<Vertex<T>>) -> Option<Vertex<T>> {
        g.vertices.difference(&scanned_vertices).max_by_key(|v| {
            g.edges
                .iter()
                .filter(|(Edge(_, UnorderedPair(e)), _w)| (**v == e.0 && scanned_vertices.contains(&e.1)) || (**v == e.1 && scanned_vertices.contains(&e.0)))
                .collect::<Vec<(&Edge<T>, &usize)>>().len()
        }).cloned()
    }

    // testing test-only code...
    #[quickcheck]
    fn finds_most_tightly_connected_vertex(g: Graph<usize>, previously_scanned: SubsetVector) -> quickcheck::TestResult {
        if g.edges.len() == 0 {
            return quickcheck::TestResult::discard();
        }

        let SubsetVector(was_scanned) = previously_scanned;
        let mut dc = g.edges.iter().fold(HashMap::<Vertex<usize>, usize>::new(), |mut h, (Edge(_, UnorderedPair((u, v))), _w)| {
            // all vertices are singleton sets by construction
            if !was_scanned[*u.0.first().unwrap().deref()] && was_scanned[*v.0.first().unwrap().deref()] {
                match h.get(u) {
                    None => { h.insert(u.clone(), 1) }
                    Some(n) => { h.insert(u.clone(), n + 1) }
                };
            } else if was_scanned[*u.0.first().unwrap().deref()] && !was_scanned[*v.0.first().unwrap().deref()] {
                match h.get(v) {
                    None => { h.insert(v.clone(), 1) }
                    Some(n) => { h.insert(v.clone(), n + 1) }
                };
            }
            h
        });
        if dc.len() == 0 {
            return quickcheck::TestResult::discard();
        }
        let scanned_vertices = was_scanned.iter().enumerate().filter(|(v, scanned)| **scanned).map(|p| Vertex::new(p.0)).collect::<HashSet<Vertex<usize>>>();

        let v = most_tightly_connected(&g, &scanned_vertices.clone()).unwrap();
        let expected_vertex = dc.iter().max_by_key(|kv| kv.1).unwrap().0;

        assert!(dc.iter().all(|(_v, degree)| *degree <= *dc.get(&v).unwrap_or(&0)), "expected {:?}, got {:?} with visited vertices {:?}", expected_vertex, v, scanned_vertices);

        quickcheck::TestResult::passed()
    }

    #[quickcheck]
    fn graph_can_merge_two_vertices(g: Graph<usize>, iu: usize, iv: usize) -> quickcheck::TestResult {
        if iu >= TEST_GRAPH_VERTEX_COUNT || iv >= TEST_GRAPH_VERTEX_COUNT || iu == iv {
            return quickcheck::TestResult::discard();
        }
        let u = Vertex::new(iu);
        let v = Vertex::new(iv);
        let expected_merge = u.merge(&v);

        let mut merged_edges: Vec<(Vertex<usize>, &Edge<usize>)> = g.vertices
            .iter()
            .filter(|x| g.edges.contains_key(&Edge::new(0, x.clone().clone(), u.clone())) && g.edges.contains_key(&Edge::new(0, x.clone().clone(), v.clone())))
            .flat_map(|x| g.edges
                .iter()
                .filter(|(e, _w)| **e == Edge::new(0, x.clone(), u.clone()) || **e == Edge::new(0, x.clone(), v.clone()))
                .map(|(e, w)| (x.clone(), e)))
            .collect();
        let mut adopted_edges: Vec<(Vertex<usize>, &Edge<usize>)> = g.vertices
            .difference(&HashSet::from_iter(expected_merge.clone().into_iter().map(|x| Vertex::new(*x))))
            .filter(|x| g.edges.contains_key(&Edge::new(0, x.clone().clone(), u.clone())) ^ g.edges.contains_key(&Edge::new(0, x.clone().clone(), v.clone())))
            .flat_map(|x| g.edges
                .iter()
                .filter(|(e, _w)| **e == Edge::new(0, x.clone(), u.clone()) || **e == Edge::new(0, x.clone(), v.clone()))
                .map(|(e, w)| (x.clone(), e)))
            .collect();

        let g0 = g.merge(&u, &v);
        let old_vertices = BTreeSet::from_iter(g.vertices.clone());
        let remaining_vertices: HashSet<Vertex<usize>> = old_vertices.difference(&BTreeSet::from_iter([u.clone(), v.clone()])).map(|x| x.clone()).collect();

        // TODO: strengthen assertions on edge IDs
        assert!(!g0.vertices.contains(&u), "expected {:?} to not contain {:?}", g0.vertices, u);
        assert!(!g0.vertices.contains(&v), "expected {:?} to not contain {:?}", g0.vertices, v);
        assert!(g0.vertices.contains(&expected_merge));
        assert!(remaining_vertices.iter().all(|x| g0.vertices.contains(x)), "expected {:?} to contain {:?}", g0.vertices, remaining_vertices);
        assert!(!g0.edges.contains_key(&Edge::new(0, u.clone(), v.clone())), "expected {:?} to not contain edge {:?}", g0.edges, Edge::new(0, Vertex::new(u.clone()), Vertex::new(v.clone())));
        assert!(merged_edges.iter().all(|(x, e)| !g0.edges.contains_key(e)), "expected {:?} to not contain unmerged edges from {:?}", g0.edges, merged_edges);
        assert!(merged_edges.iter().all(|(x, _e)| g0.edges.get(&Edge::new(0, x.clone(), u.merge(&v))) == Some(&2)), "expected {:?} to contain merged edges from {:?}", g0.edges, merged_edges);
        assert!(adopted_edges.iter().all(|(x, _e)| g0.edges.get(&Edge::new(0, x.clone(), u.merge(&v))) == Some(&1)), "expected {:?} to contain adopted edges from {:?}", g0.edges, adopted_edges);
        quickcheck::TestResult::passed()
    }

    #[quickcheck]
    fn maximum_adjacency_search_traverses_graph_in_correct_order(g: Graph<usize>, i: usize) -> quickcheck::TestResult {
        if i >= TEST_GRAPH_VERTEX_COUNT {
            return quickcheck::TestResult::discard();
        }

        let mut vertices_visited: HashSet<Vertex<usize>> = HashSet::new();
        let mut next_max: (Option<HashSet<Vertex<usize>>>, usize) = (None, usize::MIN);
        let visitor = |v: &Vertex<usize>, adjacencies: &HashMap<&Vertex<usize>, usize>| {
            vertices_visited.insert(v.clone());

            if next_max.0 != None {
                assert!(next_max.clone().0.unwrap().contains(v));
            }

            let max_next = adjacencies.iter().filter(|(v,_)| !vertices_visited.contains(*v)).max_by(|(u, w), (v, w2)| w.cmp(w2));
            if max_next == None {
                return;
            }

            let (equivalent_vertices, _): (HashSet<(Vertex<usize>, usize)>, HashSet<(Vertex<usize>, usize)>) = adjacencies.iter()
                                           .filter(|(v,_)| !vertices_visited.contains(*v))
                                           .map(|(v, w)| (v.clone().clone(), *w))
                                           .partition(|(v, w)| w == max_next.unwrap().1);
            next_max = (Some(equivalent_vertices.iter().map(|(v, w)| v.clone()).collect()), *max_next.unwrap().1);
        };

        g.maximum_adjacency_search(visitor, &Vertex::new(i));
        quickcheck::TestResult::passed()
    }

    #[quickcheck]
    fn stoer_wagner_finds_a_cut(g: Graph<usize>, i: usize) -> quickcheck::TestResult {
        if !g.vertices.contains(&Vertex::new(i)) || g.vertices.len() < 2 {
            return quickcheck::TestResult::discard();
        }

        let cut: HashSet<Edge<usize>> = g.stoer_wagner(&Vertex::new(i));
        let mut severed_graph = Graph::from_adjacency_lists(HashSet::<(Edge<usize>, usize)>::from_iter(g.edges.iter().map(|(e, w)| (e.clone(), *w))).difference(&cut.iter().map(|e| (e.clone(), 1)).collect()).map(|x| x.clone()).collect::<HashSet<(Edge<usize>, usize)>>());
        severed_graph.vertices.extend(g.vertices.difference(&severed_graph.vertices.clone()).map(|v| v.clone()));

        let mut num_components = 0;
        let mut vertices_visited = HashMap::<Vertex<usize>, bool>::from_iter(severed_graph.vertices.iter().map(|v| (v.clone(), false)));

        while vertices_visited.values().any(|v| !*v) {
            let origin = vertices_visited.iter().find(|(u, v)| !*v).unwrap().0.clone();
            vertices_visited.insert(origin.clone(), true);

            let visitor = |v: &Vertex<usize>, adjacencies: &HashMap<&Vertex<usize>, usize>| {
                vertices_visited.insert(v.clone(), true);
            };
            severed_graph.maximum_adjacency_search(visitor, &origin);
            num_components += 1;
        }

        if num_components > 2 {
            return quickcheck::TestResult::discard();
        }

        assert_eq!(2, num_components, "expected {:?} to cut {:?} into 2 components", cut, g);
        quickcheck::TestResult::passed()
    }

    #[test]
    fn solves_exemplar() {
        const input: &'static str =
            "jqt: rhn xhk nvd\n\
             rsh: frs pzl lsr\n\
             xhk: hfx\n\
             cmg: qnr nvd lhk bvb\n\
             rhn: xhk bvb hfx\n\
             bvb: xhk hfx\n\
             pzl: lsr hfx nvd\n\
             qnr: nvd\n\
             ntq: jqt hfx bvb xhk\n\
             nvd: lhk\n\
             lsr: lhk\n\
             rzs: qnr cmg lsr rsh\n\
             frs: qnr lhk lsr";

        let answer = solve(input).unwrap();

        assert_eq!(54, answer);
    }

    #[test]
    fn solves_problem() {
        const input: &'static str =
            "msr: bcd\n\
            ssq: sbl kxh\n\
            bdq: psc qxt fxm\n\
            qrt: skh lcr\n\
            lxm: jqb zgd kxg\n\
            qfm: bbq brm\n\
            sdb: mcv gqt rmx ngn tbj\n\
            vft: nxt tfb\n\
            nsc: gvg tvt pcr bkj\n\
            krt: cds bbh\n\
            mfv: rlf dbl vtc\n\
            mqs: pnl pkp ccl\n\
            bmb: pkc jpk fzc vjn\n\
            zzg: hln gbd gzv\n\
            mkl: jtm\n\
            gcj: hbk xsv dgn\n\
            rxz: jrc dkc zbv\n\
            rnd: tfg btq tdv vtz\n\
            ncf: jnf szj nmd\n\
            cvc: hbl tpf\n\
            jdx: clj mjk jtm\n\
            blh: ljb rnr hrz\n\
            rkb: znx jnn\n\
            xcp: lrf qzm\n\
            xrs: xjr\n\
            kkj: hdc\n\
            ggm: cxf kht\n\
            cvh: dmx jzr cld pmx ndf\n\
            dzt: cqd kqb\n\
            czz: mfd dpj vjm\n\
            szp: rcp dvd\n\
            vls: fdk qtg\n\
            nfm: csk rvc\n\
            pbq: dgp ctq\n\
            zdh: vff jtl ltv\n\
            csj: cck jdz lbz rkb\n\
            grk: qmh xxm dxg\n\
            blt: tmf tfb\n\
            skv: qqp chq gnf lmb\n\
            xgl: mlc jhq fbq nkl\n\
            jvt: kzq\n\
            pxs: dfk zzx xxz kkj zdm\n\
            ljz: ssn tsz mlc bjf\n\
            mrh: kqb grk\n\
            sbg: jfg jtf\n\
            hjr: vpz\n\
            dvk: fzf tkr\n\
            cxb: cpg hpq\n\
            rfn: vpq qkk\n\
            vkl: xnl rbp jqf qsl\n\
            jpq: jpz\n\
            nmd: lkq\n\
            hrk: dxq pjj\n\
            xnd: dgn bfh bqt\n\
            hrz: thv\n\
            mmx: pmv\n\
            xjf: mbm mdg fbc\n\
            cmn: dnf qvb bzn bnk vqk\n\
            ctv: mlx ztd sld\n\
            gqc: dnj brm jfc vbb\n\
            pzc: hqg zrr vbb xlb\n\
            jzr: nkl ftg\n\
            ttl: rmm dnl bqs mzh\n\
            fdk: nnv\n\
            xrn: slm\n\
            rqm: tfg plt\n\
            xmr: skp pkr nfm zjr\n\
            gsr: ltx chc bcp ksx\n\
            kpn: qvb\n\
            xnz: fdl pmt nvv rsg\n\
            phk: lln pcl\n\
            ppn: pmv kgz phc\n\
            cjz: pcl\n\
            fcz: fmt pgt\n\
            qrr: xlk\n\
            rtb: plb dpj vqv\n\
            rlf: blj lfj mpt\n\
            nsf: vzm\n\
            kdv: rqx rbh rbk sjc nth\n\
            fkp: slm nzx jrd psx\n\
            bvx: sdf zzd\n\
            mfx: tps vjm phk vjd\n\
            lzs: mbm\n\
            cld: pds\n\
            fnj: szz\n\
            zph: rxs srp nzg tdq\n\
            qdh: kjl cnc nsf cxl sxv\n\
            vkg: xdj\n\
            dkc: rxj nfh\n\
            ldl: grp\n\
            dpz: fln ndv\n\
            dts: cqz gqr zpm tkr\n\
            czl: zrp jtf xrr txd\n\
            kjt: jqk nxs bkv xsz\n\
            ccq: dlv qxt\n\
            nsv: jnf mhb ttb vbb\n\
            lxv: dch rrf vvf\n\
            dbn: mfq tnf qrt\n\
            lcl: rgz gcz lbv\n\
            nxd: hnp zkr\n\
            fvl: xjn\n\
            lnp: sgf\n\
            tqp: lnl fqr hcq\n\
            zbr: fcm pfz bvx kml\n\
            jdh: xzr\n\
            vxp: smc gkv jrc\n\
            zbc: lgg brx vpz\n\
            zbp: tvq srp\n\
            ghm: pfp sdr cld nzt pcl\n\
            ljn: zlq crx lqb frd\n\
            fnp: xpf pmv\n\
            lck: hrm jzz fmt\n\
            mth: xsx pvf zlm\n\
            rqg: jrr hcm lbt\n\
            zxx: pkp mlc xcp pht tlf\n\
            hdg: mlp gvv cns xdj\n\
            nth: vtg bkf xzp\n\
            tlt: bqs ksd\n\
            lpp: vxc qdj cpn kpn\n\
            cln: ktf vdk mfr sqs\n\
            rkh: xqk bbq\n\
            lxl: fdc dlk gdh jrx\n\
            fhk: zvz\n\
            gzh: djc qmr\n\
            jnd: pmh cds\n\
            rmr: qlx jdj vpp\n\
            mmk: fcv srl xpn\n\
            qsr: bfx pxt fkx rlh\n\
            lqr: xrr hfg xhg\n\
            qbc: nrr rqg nvb qlx rnx\n\
            fpj: cqx smc mcq dts\n\
            rkd: msr vvj bjr kfm zxp sbl\n\
            htf: mlb mcb xlb pkc\n\
            xhh: ssf cns\n\
            nfd: ggm\n\
            dkx: rnr fqr qvr nvr mfk\n\
            hjz: lqm cpg\n\
            jbl: qbq\n\
            hqn: zdg mcb qmp\n\
            spt: pzg knd hpk\n\
            ttv: tzd nnm fhn xfm\n\
            vqt: nht pbn jnv\n\
            kzx: xdk zqh lhf dhq\n\
            cfj: qsl vdk glm\n\
            nvb: tdt\n\
            gkv: mlb bhs hdm\n\
            psc: xvc\n\
            bcj: brg\n\
            tgc: tsq gvv zqh zpl\n\
            gmk: bzm mlb xmj\n\
            fjs: fzb bsb cvm\n\
            qfq: mqf jjf mkq fsd\n\
            pqn: cjq\n\
            gnq: lbt bcp hfx dfr rdr\n\
            tgt: mfr bsb vxc jpq\n\
            jsx: qgf xqs hnq\n\
            vhv: vlq vtg fxp\n\
            vqk: kcf crq\n\
            kqt: xxz pnt szt xnx hxn\n\
            tct: bcj scc kbl\n\
            mcn: qrc nfd cqx dhl\n\
            ksz: fdt jfk slj hfg cnc\n\
            sdf: hlt\n\
            bfx: pzj sbl zbv mpt\n\
            ntf: qqq jpq phl\n\
            mtg: bzk pmh ckm txx clj\n\
            gzp: fqn vgd\n\
            xcf: fkq bkl nqz sgc\n\
            dsp: ggd bjf\n\
            khq: fhk hnv\n\
            cbz: lqs hfl pds mhg hmz\n\
            ntg: qjh qxz zvz\n\
            kmn: phk qzm gzp brm\n\
            tbv: pzm txh\n\
            qrp: zsv\n\
            sgc: mkb jqf bjk\n\
            tbc: cfc fll pxb zvz\n\
            dqn: nzl xlc\n\
            tkz: mjk mmv\n\
            lnh: rpm xqp\n\
            hsr: lrr rvf bfn\n\
            xvb: jvb lhr\n\
            mbm: xjn\n\
            ptc: ppp mnp\n\
            gjb: zvz\n\
            jfg: grd\n\
            fsp: xmb dgx\n\
            lrc: jtl\n\
            zxp: cgd tnj rqr\n\
            mdb: ghc\n\
            xmb: mjz mnt\n\
            qcv: gcj ctv cpn lbv ccq sld\n\
            cdj: czv qdr kcv\n\
            gfb: vdk\n\
            bfk: cqd mlp vtz cbp\n\
            xsx: jhq jdx dcj\n\
            bns: vnr kxh\n\
            bzn: vlq\n\
            grl: szp grp zbp pnz\n\
            tbh: flh fxm spm dkl\n\
            cgz: lzs fxk lnx zbc\n\
            bdf: cvl tlf xth gns\n\
            nzg: llz lrc xdj\n\
            gmt: plt tln lpp gcz\n\
            gxd: bgq dhk pbn nmm\n\
            pzj: jvb\n\
            lfd: ggm\n\
            vkx: slj cdv ztd\n\
            zpd: fnx fcp dgb\n\
            cks: bzm\n\
            rpl: dbn qcx tdq xfh\n\
            vvx: ndh sqf lrf fln\n\
            srt: pld lhs jrb zxz\n\
            vdv: qcx tdt\n\
            vzm: qlq\n\
            xtb: szj\n\
            rnh: jjr\n\
            mlz: vjd blk\n\
            crr: qmp gns\n\
            qqq: lks\n\
            ljk: fhq zjr\n\
            jxj: tcn rdq qbm\n\
            lxc: nlr lzl nxz trg\n\
            fdl: xjr lrr\n\
            fll: xxc\n\
            xld: dlk kcv\n\
            mfk: pnt lks\n\
            fcm: jpq jpz\n\
            flg: kmx qjh fnm\n\
            gnr: vls\n\
            nnt: plj ljb vdl\n\
            jgm: svp csk\n\
            kff: tzk hsz cck kcv\n\
            mnx: cdl vdl dnq\n\
            nhs: qmh bkv fdk qfd\n\
            lrf: bnj\n\
            tbk: hcm kvx\n\
            pvh: vgd vdn cms\n\
            mcv: jjf fmh jfg\n\
            bll: tkq dnf mlp\n\
            sgh: pll bbt jnv\n\
            lxx: jbf\n\
            rzb: ffp lrc xdk\n\
            xbm: szj cks ngb snz\n\
            ljd: fvz lkg kcf\n\
            njs: dgp zhk spl zdg bcd hjz xrs\n\
            knr: pzg mmv zsv mmk xlg\n\
            clj: xmp\n\
            tfr: jkg nvd fdl qls\n\
            fqr: mdb lbv qgf\n\
            vcd: tpp qqp zxs\n\
            vkf: crr jvb nfh qfm cts\n\
            xlc: pmf rqx\n\
            vpn: hcm drz skh lxr\n\
            hcz: zhp pqx fvl\n\
            ljt: fqn mvs\n\
            hpk: vkz\n\
            pfd: tnj xcp\n\
            pmx: tqc\n\
            qrv: tjj tkx bfn bzq mlz\n\
            xfv: plb\n\
            bgj: ljt qgj dhl\n\
            hnb: ckq qqr klm fcm\n\
            sld: ghc\n\
            stj: dbl\n\
            czr: gff\n\
            rhj: fmq xgr mjz zjr\n\
            tjj: qlt ckx rxh\n\
            bfb: jzr xfv mzf gsc\n\
            qlx: bqf\n\
            ctf: mkq\n\
            jrd: hpq\n\
            zms: zdt kht krc mph dbj\n\
            jjf: brx czr\n\
            tvq: brx xvc\n\
            bbt: grk\n\
            bqd: nsc rdb xpl zdx\n\
            tdq: tmb cnc vdl\n\
            fnc: lcj ncp dvd pkr\n\
            gdr: gjx ssm psk hkd tfg\n\
            qxz: hjc vfd\n\
            tmf: vpz nlp\n\
            sbr: pjj vhk trz\n\
            pqg: ggd bqs smd nlf\n\
            nks: xxm\n\
            hrm: bcp dnx\n\
            rlh: fnp jdf\n\
            frh: nkh xhg\n\
            psx: fpg jbt\n\
            lhf: hdq fdg\n\
            mzt: hsc kcv\n\
            nxt: drn rgz\n\
            nht: khq vdl xdb\n\
            nsx: dch\n\
            lpz: zpl qpp lxr ptl hpp\n\
            flv: kqr rrb pkr mfq\n\
            gvr: kbs qlq\n\
            lrs: jbf dth jlr sdr spz lnb fpg\n\
            mqx: qpp\n\
            nvp: czr tfb kfl hkd crx\n\
            tmb: bpt ttk\n\
            rvn: gvv fnm vft\n\
            bvp: gtd grx rqq\n\
            dnx: crq\n\
            zjp: tqc mmx\n\
            tlk: fqn hrp pzm xxs lvg\n\
            flh: sxn ktf\n\
            nlp: lcr\n\
            fzc: rlh\n\
            nkh: dnq brf xgr\n\
            bzq: bkj xqk\n\
            svf: vdv nrl vcd tqp ljd ghl\n\
            vzr: mnp\n\
            llk: tpp qpp qvq bqf\n\
            rdq: phc mhb dlz\n\
            bzk: zqr mvf sdr\n\
            fkq: fhk fmt\n\
            knv: rrs\n\
            bpt: plj\n\
            lmf: stt fmf xfh zpk mjd\n\
            zxs: dlv bqh\n\
            xhm: tlk dlt zdc\n\
            mmv: fbt\n\
            rfx: qdj fxp mqf\n\
            zlk: xpl vdn jnn zdt\n\
            xpf: xpn mnp\n\
            cpb: lbt qlb fjs bkl\n\
            jnf: lmz\n\
            tjs: cdl zjr spm\n\
            blg: gbx mnp\n\
            jtm: prv\n\
            vlb: ggj zjx\n\
            qjr: jdh hjd vpf srl gzz\n\
            kfb: hcn fps jzk lbt\n\
            lqq: gcb vtc csz jrd\n\
            ltx: jfv\n\
            mbk: dvd pnz brf\n\
            mqk: mqt tzd mfk vfd\n\
            hsz: jrb\n\
            tzp: nrm lnp zkq\n\
            rcp: sdf kcf\n\
            ljb: mjz gjx\n\
            cpg: vkz\n\
            vkr: mlx zhl rzq\n\
            lsz: tcg gpj sjq nmm\n\
            qgc: xmn nrn bzq kfm cnj pvf xmp\n\
            mfq: flg pdh\n\
            xtk: nnv\n\
            kvr: pld ftg chr ppn\n\
            bkl: dkl\n\
            plt: nxd qjx\n\
            lkr: bjf snz pzk\n\
            fgh: hfk nqc pnt hlt\n\
            hqh: lsl fsd\n\
            hbq: tlj gpn npj ngp\n\
            mkh: pkj sxp qgn\n\
            cqj: xqc qzm nrm nsd\n\
            ffv: qzt tkr nnp hjv pdb jxj\n\
            glm: ldl lsv\n\
            xdk: kqr csk\n\
            sgf: jhz cds\n\
            sdr: zlc jrx\n\
            ftr: ssm vdk vqg\n\
            xpm: jql tkh\n\
            zhl: sgh fhl\n\
            kdh: ksm ntb zmq tbj mjn\n\
            qgf: jtl\n\
            bmd: cvc fhq ngp\n\
            lqs: xlg qff jdz\n\
            dhh: jmb\n\
            nkl: lvv nrm fcp\n\
            lvp: lbq msc cjz mmp\n\
            kfm: tzp hdm\n\
            rnk: bcp\n\
            xfh: jpz\n\
            fcv: kcp zlc\n\
            sdz: gxp jkf vbb glz\n\
            tkx: xpn\n\
            vpz: xxc\n\
            gcb: lbb zlk nrn\n\
            fmf: zrf ccp vff zdm hqr\n\
            kqm: vpt lld xxz\n\
            fbp: fxp qjj nnv qvb\n\
            dvd: szz cct\n\
            sgz: skh\n\
            qbm: fbt krt\n\
            gbd: csz cds\n\
            vvj: bjr qrp\n\
            tqh: xjr frn dpg dlv\n\
            bsj: zzh fsd hfr bmd\n\
            vrd: fqs jfv jtf zmc\n\
            gns: cjz gpq\n\
            pkj: sgf\n\
            zkr: fpc\n\
            pgh: tlj pcr pvh\n\
            rdb: zqm ljf trg\n\
            ksd: nmn\n\
            tdv: krq dbb lpl\n\
            lkv: bns kcv\n\
            hjh: hfr kcz\n\
            zlq: kbp zhp\n\
            pgc: qrr mkb dhq ftm\n\
            gdh: ssl tqc\n\
            pxt: gqr xkh\n\
            qjh: ktf tmh fxm\n\
            jck: hsz kfz kht gcv\n\
            jkc: knh mqx plt xsf\n\
            dbb: vpp llz nlq rcp\n\
            rpx: pxn pgt qbt phl\n\
            zlm: tsz ccl nvv rnh\n\
            nnn: dgx xxm fdg\n\
            xpz: kqb\n\
            qfd: fmv hjh kvg\n\
            mgl: dhh\n\
            htt: vns tnf zng sxz tmh\n\
            jkf: lkr\n\
            vtg: sgz xxc\n\
            jxv: gpn rgn jdf rjn\n\
            srl: pvf\n\
            ghz: dzv\n\
            xtp: ctq cgd\n\
            gtt: vpn bbt spm kzg\n\
            vvc: plh fcd ffp fmv\n\
            dgm: gzv rxz chr vgg\n\
            sht: fsp tds nks xqs\n\
            dsm: xpz vvf hvx jsx\n\
            mzh: lkz nmd\n\
            vqg: vjz fgb\n\
            qvq: khn mnc tfc rgz\n\
            pdb: bbq rgx\n\
            qcx: pbk\n\
            kbq: cct qxz fvz\n\
            mxl: nqt zlq zkr\n\
            qlt: nzx jmb czv\n\
            rrb: ptp cbp\n\
            bbc: dfj ltm jkc psz\n\
            zmr: lkq lln stj\n\
            cvt: khq nsf vtg\n\
            bvl: bnj\n\
            dlg: rsr cds\n\
            cxf: zdg jrb\n\
            gpl: cxl tfv lld\n\
            spd: hfg qxt\n\
            fmj: rbp dnt kqm ftm\n\
            rqr: prv lnh\n\
            pbx: zfj vnq qgn\n\
            hxq: ggr dnl jmc rqp msr\n\
            vjd: hnz vvj\n\
            bpg: cmf pkc plb ckx\n\
            xkh: gzv zpm\n\
            xjj: jkh nzt pcr sgs\n\
            lrr: gxp ndv\n\
            qdj: cdl\n\
            vgg: zsk kcc nfh mtg\n\
            kbv: vdk klm hcn tpf\n\
            vhk: vkg\n\
            hxn: psk sgz\n\
            cfg: bjf sxp lvv kmz\n\
            xgm: qmp ppp\n\
            jms: hcm\n\
            nxq: phv zbx nbt mlh\n\
            dnn: ngb lkk xlb\n\
            vpq: hfr\n\
            gpj: lcg vqt bbt\n\
            jpn: jnd qrp bns\n\
            zss: xqp jnf xmj fbt zjx\n\
            plh: rhj kkj\n\
            zlc: fpg\n\
            bcm: ttm bcd\n\
            qlb: dbh\n\
            pjr: rbh xsl ngn thv\n\
            rhn: srh rdr tnp bdq\n\
            mqz: vqv lmz\n\
            fcd: bdl\n\
            jgp: xpl crr tbv lgc\n\
            gjp: tkq lks\n\
            cts: qgb tvt prv\n\
            fmq: hnp grd\n\
            qch: vrk\n\
            rxp: sgz hdq mqx\n\
            ptl: llz fhk ldl hnp\n\
            ngd: cnc hrk zvl\n\
            fnq: hdc\n\
            ccp: sbm fgb tvq\n\
            ntb: bkl\n\
            tzs: nmn mkl zqr cgd\n\
            zjx: zgd\n\
            dgx: jvt\n\
            pnt: lcl\n\
            ddf: fkx ddl hln fbk\n\
            dhp: gmt zzh xdh bjk kfl\n\
            tzd: qmh vpz mmq\n\
            rhf: mkq mnx\n\
            blk: nzx\n\
            vqv: mhb\n\
            nlr: cmf cnj sfj xrs\n\
            mzq: kht\n\
            xjr: lkz zqq\n\
            vnf: gmk cbd\n\
            ddv: qfg srr ljm jdj\n\
            fbk: trg dhh qzt\n\
            rtc: szt bmf bkf bln gfb sgg\n\
            txd: xhg dqn nxs hpp\n\
            bqt: vrg\n\
            prk: mqh kcc fnp\n\
            fcp: jjr\n\
            vkb: mqh hpq tps lhs\n\
            zqh: rfn nlp\n\
            sqf: jdf zxz jlr mmx\n\
            jhg: ksx nqt cjm fqs snd mzj zmc\n\
            qqr: tjs kzm\n\
            zrr: dlz sqz vzq\n\
            bjk: vkg mqf\n\
            dth: vcn mkh lnb\n\
            nrh: mqh\n\
            fpp: tmh qgp mfk xjn\n\
            hsc: jhz pcm\n\
            rmx: psz rrf cpn\n\
            pkz: gcv pmz gsv fzc dcs\n\
            dtc: vpq nxs drz nxd\n\
            xzh: blk lbb cmf\n\
            ngn: jrl csk fkq\n\
            jkb: hpq zdx mkl jdf\n\
            nqt: tbk\n\
            crf: bsb cxl dhk rxs\n\
            bkq: szj chr czz\n\
            tfg: qzc fsd\n\
            gnp: tkx jkg tmq fzf\n\
            jhq: zdt\n\
            hfk: nnn htc qqr\n\
            nhn: ckq jvt rbd flh\n\
            cqn: dpj sgs ghz dgb\n\
            tgl: hlt qrr hnv cbs\n\
            lrx: txh qfx\n\
            bqh: skh\n\
            hkd: vqk\n\
            dtg: ltm rnx rqm dlv\n\
            dfc: dgx lgg pfz ccp xxm\n\
            gzr: srh sgh lzb fxk\n\
            trc: sfv jms xdh\n\
            nnc: brg sqz dkt pmh\n\
            mpb: vrk pkc\n\
            vsq: vgd phk nzx\n\
            hnf: xtb qmr nnr gzh zcb\n\
            mvf: nvd pfp lhr\n\
            mpf: zsk lnp cjz\n\
            tfc: hrn\n\
            kzg: psk jgm\n\
            lkk: cms\n\
            mhg: msc\n\
            zpk: czc dgx ftr bqt\n\
            shr: kvx zjr sbg\n\
            rxh: mgl\n\
            mqt: bzf ssf ttk\n\
            kxg: fnx blv rmm\n\
            nrn: cts jgp\n\
            fhn: fvl tkq hnp\n\
            tjp: rvn bln hrv rcp\n\
            bln: zkr\n\
            zfq: rqr bzm xqp\n\
            mdj: ckx rxh gqf tzm\n\
            zxc: hjr knh mbm\n\
            ggc: cck ddn ngp cms qnm jsr\n\
            ssm: zzh tkh\n\
            tpp: mmq tdt tmb\n\
            hrp: nmd\n\
            fxj: blh gmd fnq cct\n\
            lkg: tds xlk bqh\n\
            ncp: kcz tmh zvz\n\
            sjc: sxn\n\
            vpt: fpc ncm plt\n\
            qzc: dfj qjx fxm crq\n\
            shl: ktq ddn xld pzj nsd tqh\n\
            zng: vkx tfv\n\
            jzg: mpt tlf jxs qzm\n\
            gsv: bvl zsv vtc\n\
            rvc: jvt tnf\n\
            ddn: dpg lkq\n\
            fps: vzn fcz rnk\n\
            lcg: kpn mnt\n\
            rbh: cdl mbm pqx\n\
            rts: zkq djc bhj\n\
            kzm: ztm\n\
            zbv: pzk\n\
            mcb: rkb\n\
            kcc: mqh pmt tcq\n\
            dlt: fdf mzs gdg\n\
            zmc: fdx vgh\n\
            rpm: vcn\n\
            tnd: pnl fcv gsv xqk\n\
            ptp: nbb\n\
            zdt: lln\n\
            lbq: gqr lgc\n\
            zvl: tkh nvb\n\
            nss: pxn jvf drz qlb mqf tpp\n\
            xlg: tsz\n\
            bzm: tps\n\
            bhj: mzf pkc\n\
            cvl: xqp\n\
            lnl: mqf spd mnc lzb\n\
            xrr: phl vxz\n\
            dlk: jrd hsz\n\
            xcg: ggj phd lkq\n\
            hhj: plh ntg pqn zxs\n\
            lpk: hjd dkc lrx zml\n\
            pnr: kzq xdb ntf xsv\n\
            fxk: dxq gff\n\
            vzq: nrh pcm\n\
            rbk: zzh lxr\n\
            dcl: tpf\n\
            nrc: vxp rqq pmt ccl qls\n\
            pfb: llf svh jzz\n\
            mzj: dlf hxn kkb\n\
            gzd: fmq btq tnp hbl\n\
            smd: glv\n\
            gzz: rvf mfd dlz\n\
            rrf: mnt\n\
            vhd: bkj skt mvs tjf\n\
            jsd: vbm qnj vnr bjr\n\
            mbj: kpn\n\
            hlz: qkt cfg lvp dpz nsz gpf\n\
            scb: bcm tlj\n\
            kmz: rpm\n\
            mrz: rfx tcg qmh tfc\n\
            nph: nbc ctq pmh zkq\n\
            ncm: qdf kjl sjq\n\
            gxp: rjz\n\
            nvr: nmm\n\
            thv: fcd\n\
            stt: pmf drn xzp\n\
            xsf: nrr\n\
            gjk: ncf mzh tzk\n\
            vxn: tmq hrp nvv mpb\n\
            chc: ntb grp\n\
            bsq: fqk cjq bcp krq\n\
            nlq: skp vlq sbm\n\
            rnx: cbs mlx vgh ndr\n\
            phg: jgm xzk trc rqx\n\
            znj: krt xxf xzr\n\
            nrl: tgt sxn\n\
            sdk: djc cvl bcm qrp dhh gcv\n\
            fbq: gqf\n\
            glp: zfb lcj klm tln\n\
            cqz: dlg gtd\n\
            hrv: pqx xpm\n\
            rhc: zms prk cxb krc ndv\n\
            slm: jrc\n\
            dlf: khp kbp\n\
            jvd: kcz dzt fdx\n\
            fdf: blj\n\
            pzm: zgd\n\
            vxm: znx tlt qlt gdg\n\
            fmv: gff xlc\n\
            dpn: hhq jhd tds pqx\n\
            hkr: xdj hcm\n\
            jpp: thh cks\n\
            vfd: fgb dgn\n\
            vnq: jjq tzm vnf\n\
            dch: fsd\n\
            ztd: hfg rnk\n\
            nbd: scc gpn vvj\n\
            tpf: qvb\n\
            pkq: ddf vkz pmx xpn\n\
            nkt: njv gqf ckt lgm jrb\n\
            pkr: nxd nks\n\
            ndf: bzr cxb\n\
            dzp: qch lfj vcn\n\
            zth: mtb bql qnj pvf jkf\n\
            fbc: ktf\n\
            dmx: fkx nfj mzf\n\
            pnl: jnn\n\
            nnv: rdr\n\
            sfv: vfz rbp\n\
            jrl: gvr mtp szt gcz\n\
            hpx: qlq xhj lzs dfj\n\
            zst: dkg bsx nfj gbx tzk\n\
            fvp: nbt tzm fbq scb\n\
            qpz: fkx hjd dzv\n\
            mpz: czc jbl lzs dnt\n\
            xsl: nzg jlp khq\n\
            tmm: lgc vvj jdh pzj mlz\n\
            jpk: gpq mzs qgj\n\
            dhq: mbj kvx\n\
            czc: bfh rbp\n\
            qfg: cvm rkq qvr\n\
            tlj: dzv\n\
            bgq: lzb\n\
            zpl: cjq\n\
            ckt: qgb jvk tjf lkf\n\
            kbk: vzr fdl xrn fxd\n\
            hsf: hcm bdl\n\
            frd: nmm\n\
            sgs: tnj\n\
            rjz: tlf\n\
            hdv: pdh bkl xjn\n\
            mrr: bvp tct kmn\n\
            xrb: smd jpp vrk rrs mth\n\
            hmz: sqz zgd\n\
            cck: gtd ghz\n\
            qqg: vlb rbc fpk bfz\n\
            qkk: lcj cbs\n\
            pvf: qks cld\n\
            qvr: jjf jgm\n\
            zdb: ctf tdm hdq\n\
            ccd: qfx pkj sqz\n\
            gzl: fsg vpq dch\n\
            fdc: cbd ptc vzq skf jxs\n\
            ttk: hpp\n\
            tbx: lqb xsf sjz nrr fll pdh qpp\n\
            cvm: tbk rbk\n\
            jsr: grx nsd slm nrh\n\
            xqg: ttb bvl mqz mcn\n\
            qzt: rkb\n\
            xlr: qtg dxg gnr vbv ltm\n\
            ttt: dhh vcn krc\n\
            qfx: hgz\n\
            cqx: lkk jrm\n\
            nqz: ljk sgg kzg lcg\n\
            hdl: dkt xsx xrs fpg nmn\n\
            nnp: jdh mlh zxf\n\
            zqq: czv tkx\n\
            bzf: hrv pbk jtf fhq\n\
            tkr: gpf\n\
            fvz: vvf\n\
            psf: stj dkc dpg\n\
            lts: spv lqb klm kld qxm\n\
            cbr: ddd ckt cqj plb\n\
            rdr: lks\n\
            xsv: dkl sld\n\
            pmh: tkx\n\
            pht: jdh gbx dzp\n\
            zhp: qdf\n\
            gff: fvl\n\
            svh: ldl\n\
            ljm: jpj hcr xsz xjf\n\
            tln: kpn\n\
            skt: ttm gdg pdm\n\
            dkm: nbt bfz bbq kxh nzt cdj\n\
            vrg: dnf cqd kzq\n\
            pxn: nvb\n\
            rpt: dvk pmz zfj dnj\n\
            gzf: zqm txh hfl lfd\n\
            crd: hfx hsf fsp\n\
            nbt: tsz ttt\n\
            ntt: htc vdv bnk mbk\n\
            sjk: mzt mvf kgz hnl\n\
            ddd: jxs\n\
            qdr: lkr\n\
            rbc: fdf pdm pzk\n\
            lsl: ljg\n\
            dlz: qrp txz\n\
            kbp: jfv kcg\n\
            lbz: jrx ljt\n\
            pkc: vgd\n\
            qks: glv pcl\n\
            fkd: qsl qtg jms fbr\n\
            fpk: zjp ghz xxf\n\
            rsr: zsk lkz hnz xxs\n\
            xlk: rgz\n\
            dfj: rgf\n\
            lqm: kgz tbv\n\
            vns: rgf\n\
            ggd: cxf\n\
            gjx: qtg rgf\n\
            fln: ssn rts\n\
            sqh: pkj rqp qch rzp\n\
            lbv: cxn\n\
            dpg: rqq\n\
            gpf: pxt\n\
            kbl: zqm gfc sxq\n\
            zxf: mhb\n\
            zml: mdj znx\n\
            njf: sjc hrz nqc kjl\n\
            ncz: vpf sgf knd gcv\n\
            szh: gqt zxc xgx pnt\n\
            mzf: kcv mmx csz\n\
            xfm: sjc rvc dlf dqn\n\
            rln: qtg dcl psz prc\n\
            nsz: xvb ngp\n\
            zzd: gfb\n\
            gzv: lkz\n\
            pxb: zpl qmh crd\n\
            lsv: qjx plj pfz\n\
            ghl: vdk fdg mqf\n\
            fhq: csk\n\
            fsg: gfb qgf\n\
            lrp: krc xss bbq fjd lmz\n\
            ljg: ksm fnk kfl brx\n\
            jlp: fnj hfx plt\n\
            thx: zbx jdf kfz\n\
            cjm: xlk qpx\n\
            tnp: nnt sfv\n\
            jds: khc jxj bsx ssn\n\
            vjs: mjk\n\
            prh: xnx pnr xtk fdg\n\
            xhj: fnj lgg vgh\n\
            nzl: ghc xlc lbv\n\
            slv: fll svp cxn\n\
            jlr: chr vkz\n\
            zrf: qsl rrf zhp kmx\n\
            bxp: mmv hdm xxf\n\
            mfd: tqc\n\
            xss: czd lxm blg\n\
            jjp: lhs rkh bql mqs\n\
            cnj: mjk rqr\n\
            bvm: mjz nmm sjq tpt\n\
            dbl: xtb\n\
            zhk: hqg lfd lqm\n\
            gsc: spt dpj xfv nrm\n\
            mcg: xtk\n\
            sxv: hhq dxq\n\
            qrc: dkt pds rkb\n\
            qsk: bnk dnt sxz\n\
            zjr: cbs\n\
            btq: jzk xqs\n\
            ckm: vnr tcq vjs\n\
            jlk: rmx kml pnz ljk\n\
            zpr: phk bhj xfv tlj\n\
            ndv: lgm\n\
            ckx: cms\n\
            qxx: tbj fcd jzz\n\
            zrp: jql hcz rhf\n\
            grd: bcp\n\
            qgn: qdr mvs\n\
            spl: bnj hfl\n\
            trk: bnj hsc hpk stj\n\
            tlz: hkr qqq jdj\n\
            xxc: lnx hbk\n\
            bqs: qmp\n\
            gsl: xpm xdb bvx dnx\n\
            mpk: srh qqb vns dhk\n\
            rxj: qnj pdm vkz\n\
            pqj: hjh svp vqg pxn\n\
            mnc: vkg\n\
            zcb: thx ctq mfv\n\
            clf: pmv lbb vnr kxf qpz zdc ktq\n\
            kld: trz hdc\n\
            ggr: bhs jrm gkv zpm fcp\n\
            kpc: zfj rlf dvk shq bnj krz vjs fzc hnl\n\
            jfk: vfd vbk\n\
            klm: tdt\n\
            mmp: rxh vnr nrh gqf\n\
            kfz: jkh tvt gpf phc\n\
            ldq: nbc rqp skf zjx\n\
            rcz: xxs tnj sdr rvf\n\
            hnl: nrh\n\
            rkq: tmf\n\
            hgb: scc rgx shq zsk\n\
            qpx: hjh hnv dgx\n\
            tdz: kqm mqt vdk lck mrh\n\
            gpn: czv czz\n\
            qpg: mpf jfc lxx\n\
            nvk: tsv nzt xtp tcq\n\
            zfn: hbl flv gqt qbt\n\
            dxl: dhl bfn zqq\n\
            hrn: qbq thv\n\
            vxz: mlx\n\
            khc: ngp mfd\n\
            hbl: qlx\n\
            fhl: vhk lsv\n\
            xct: spz ngb lhr kgz csz mkj\n\
            szz: kbp fnm\n\
            nqc: bkv grp\n\
            dnq: vbv sfr\n\
            mlm: vrk xmp kbl\n\
            hqg: dlg bdf\n\
            cxl: xlk jhd\n\
            hcr: mdb kcz fdx xhg\n\
            ttm: mzq\n\
            zxg: fdx lxv hkd mkq vfz qjj\n\
            zmd: mjk rgx jhq ffv\n\
            tsq: fdt dnt hjc\n\
            bdj: hnq fhk\n\
            ddl: qfx dlz\n\
            bhs: ggj\n\
            xdb: gfb\n\
            rsg: hrp zxz txz\n\
            plj: vjz\n\
            dpd: cbp ppz hhj xdh\n\
            vtc: gtd\n\
            sxz: mrh gfb\n\
            sgg: hqh ltx\n\
            jbf: ssn\n\
            zdx: mcq jxs mpb\n\
            rbd: nnm gnr mnt mkb\n\
            xcs: tbn vjz cbs dcl\n\
            dkl: crq\n\
            hnq: nvr\n\
            rnr: svh\n\
            gjf: ggd hqg vjn khc xcg dxl dpj\n\
            xjg: bgl vtz mpk ncm\n\
            xmn: txz glv tsv nfh nbd\n\
            qjj: jql dps\n\
            khp: skp fgl nth\n\
            phv: blk rnh knv\n\
            ljf: xxf bjf\n\
            hvx: ffp vqm bjk fhl\n\
            lvg: tps nrm\n\
            hdq: lnx\n\
            ttn: qff mlb bfn qbm\n\
            slt: llz gjb chc fdk\n\
            vjn: qnj gtd ddd\n\
            jjq: snz pld gbd\n\
            xsz: nks jnv\n\
            fjm: lrr hfl dpj zml\n\
            gmd: hfx nsx qxx\n\
            prv: zdg znx\n\
            dcj: vlb gxp\n\
            snd: nfm zpl\n\
            vkv: ptp zkg bgl xxm vzm\n\
            lld: jtl cns\n\
            gbx: ftc lpq nnr dnl\n\
            jbt: lqs zjp lbz\n\
            jvf: qrt hdv kzq\n\
            rgn: vdn\n\
            nlf: gmk gpq mvf\n\
            fkj: blj znj lhs bgj\n\
            llf: hjc\n\
            xzp: qvb\n\
            kqr: vvf\n\
            qrq: xpz knh fcz llf\n\
            jvc: lsl vzm\n\
            vvf: vxc\n\
            lqh: dbh xnd xxz rqv qqp\n\
            vpp: skp\n\
            bft: zpl vpz xhh\n\
            xtq: rqv fvl fhq sxv\n\
            kmx: nsx ztm\n\
            jzk: tbj\n\
            glz: jjq nvd\n\
            nbh: fmt xgr drn sbm mqx\n\
            knd: lxx jnd\n\
            jhj: nfd jkh bzr\n\
            rmm: qdr bcj\n\
            xdm: fnj tdz ctf kzg\n\
            xqs: mnt bdl\n\
            vpf: cqz rqr\n\
            qjx: qsl\n\
            xzk: fbr dfj\n\
            sqs: pfz fkd bgq bsb\n\
            hdm: jbf\n\
            lcr: vpq hjh cct\n\
            hln: qch npj\n\
            prz: fhq bzn xnx tkh\n\
            jkl: zdc lkk xgm\n\
            rzp: nzt ljf jpn\n\
            ffd: lgm mkl xlb\n\
            mcq: vrk xtb\n\
            mns: snz bhs sqp zqr\n\
            tcx: rxp fpc pll\n\
            ftc: rvf jjr hqn\n\
            bbh: qkt\n\
            zqm: blk\n\
            spq: qbc dnx cvc lcr\n\
            txx: mgl jsr ttn\n\
            gqr: bbh\n\
            lzl: qzt qkt xlg\n\
            pbn: pmf qbq\n\
            mdg: frh mnc drn vhv tkq\n\
            pll: gjb kbp\n\
            fkn: scb lpq gfc qgb nsz\n\
            dzz: gqc qkt tjf jrm\n\
            rxx: pgt mcg tcx sgh xgx\n\
            vtm: mkj dzp lfd ppp ddd\n\
            qgj: bvl knv\n\
            rdd: rgn sxq fdf brg\n\
            tnj: ksd\n\
            vjz: bqf\n\
            phc: lln xxs xzr\n\
            kxf: cbz ckm zbv\n\
            svp: kqb\n\
            dcs: vzr rkh\n\
            tqm: qlb pqn xtk hfr fsg\n\
            sqz: ttb\n\
            lff: vft prp kcf\n\
            vcg: xgm bkq pvq cks\n\
            czd: pmt dhl hgz\n\
            jdz: cgd\n\
            qgp: rkq zbp jzk\n\
            tcg: pzv jbh tbj\n\
            xxz: qrr\n\
            tdm: ftm jzz vxz\n\
            frn: jnn zxf ksd\n\
            ppz: lld kcg\n\
            bql: gng lbq ptc\n\
            bfj: pvq nrn lrx xpf\n\
            kcp: jhz kxh gqr rjz\n\
            tpt: hhq gfb kvx\n\
            gvg: lvv lnh npj gdg\n\
            xpl: sxp\n\
            fmh: bkf sxn xqs\n\
            qnm: ndh tsv blv ftc jkf\n\
            fqk: fmv rqm tfc glm\n\
            cxd: xgx psc gvr hpx\n\
            pgp: clj glz ttm pfd\n\
            srr: pfz kld\n\
            bnk: hdq\n\
            jbh: xlk mcv hjr\n\
            dgb: pds\n\
            jpj: bzl mcg hdc nqt\n\
            gnf: vzn ltx hrh rhn\n\
            fzb: hqr fbr jvc\n\
            shq: phd\n\
            crx: xnl fnq nsx\n\
            ngp: lvg\n\
            xdh: kvx\n\
            bdl: cpn mfr\n\
            txz: lhr\n\
            tdr: mnx bpt nbb vbv\n\
            cms: xmp\n\
            tbp: srh tds qcx hrz jbl kzm\n\
            ttb: jtm\n\
            pzb: ssq npj pmx lnb\n\
            lnb: vjs\n\
            qff: jnf nsd mzs\n\
            sjz: vzn hrn tll jtl\n\
            rzq: nnm pgc zdh qcp qsk bft\n\
            pjj: cxn xvc\n\
            fzz: dzt hhq lnx kqr ffp\n\
            sfj: dpz jkf pvh\n\
            skb: sxp zxz mvs\n\
            nxb: pnl lpq jrc fkx\n\
            dnf: cfc\n\
            fzf: bcj sbl\n\
            nnr: lgc tsj\n\
            xqk: bbq\n\
            hrh: psk blt qpx\n\
            qlq: hfg\n\
            nbq: kml qqp phl\n\
            cxn: skh\n\
            zkg: rnr gpl kzm vbv\n\
            dfk: xtk ksx mcg\n\
            mkj: gxp\n\
            lgt: jmb bkq zzg tbv\n\
            lmb: kbs bqh slv bzl bbc rrb lhf\n\
            cbp: fnq qdj\n\
            rgr: tfb lpl nzl vzm\n\
            khn: pqx gnr tpf\n\
            ksk: qqb dgx blh bmd\n\
            jhd: rvc fbr mbj\n\
            xnl: srp\n\
            bgl: nxs\n\
            ftg: nvv cmf\n\
            kbs: jbl jfg hlt\n\
            rfg: tmq rtb nrh tqh\n\
            bfh: mbj lgg\n\
            jqf: zvz\n\
            fdg: trz\n\
            jfc: rgx\n\
            bmr: lmz tcn xrn mph\n\
            qxc: bgq kml mkb ndr\n\
            ndr: fbc krq\n\
            bdr: qjh rqv nxt fvz\n\
            fdh: sbr mxl vpt hpx\n\
            dfh: jkl gzh zsv zbv\n\
            njv: bbh\n\
            pmz: qks hpk\n\
            kvg: bkv nbb hdq\n\
            qsf: jfg nks gcj jrl hkr\n\
            fgl: zzd flh vff\n\
            cbd: cvl mqz\n\
            hbs: dsp ccd qgj gfc\n\
            pld: mqh mvs\n\
            ppp: gzv\n\
            cdl: rfn\n\
            fbt: qzm\n\
            zfb: vqk nbb xvc sjq frd hrk\n\
            gqt: hpp\n\
            zmx: fnk pbk bln hrm\n\
            txh: dbl\n\
            ssj: dzv nvd qzm vnf\n\
            bfz: zjp gbx\n\
            mlp: dch\n\
            dbh: fnk rqx\n\
            clt: qxx rvl ltm mpk\n\
            bzr: lgm brm\n\
            htc: gvv vhk fgb\n\
            xgx: gjb qxz qdf\n\
            rqq: pdm\n\
            vgh: trz\n\
            drr: xtp nfd zsk mtb knv\n\
            fkv: qlh dxq fjs mjd\n\
            hqr: pzv hnq xpz\n\
            hcq: lsl fbr gjp\n\
            jjg: skt ngb bcm szj\n\
            cdk: jtf spm jfk mrh nlp jpz\n\
            qqp: ztm\n\
            tzz: hnl mrr xpf tsj\n\
            lvv: xmp tvt\n\
            slj: nzl mfr\n\
            grx: qfx xzr\n\
            zbx: cpg bjr\n\
            jhf: tjg krt rnh scc hpq\n\
            qzz: xmj qnm ssj fxd mnp\n\
            rvl: cvt sdf hcr lff\n\
            fpc: bqf\n\
            snf: fmf sjc nsf lck\n\
            bsx: ddl xzh\n\
            vjm: jkg xxf\n\
            btn: hsr lrf mcb ndf cxf\n\
            bcd: glv\n\
            tll: hjc pqn\n\
            dps: czr tln ksm nlq\n\
            dxg: ccq fxp\n\
            mjd: kbq mnt\n\
            qgm: vbk grd jnv bdj ptp\n\
            zqr: jrc dnl\n\
            ztt: kjt cns zkg xfh\n\
            jsg: nrl tpp ckq tzd\n\
            gzb: dcs mlh zqm kmz cbd\n\
            kdx: hsf cbp tlz cjq\n\
            dkg: djc xvb\n\
            bbq: tlf\n\
            jqk: pmf zvz\n\
            pvq: qgb sxp dgb\n\
            qmr: hjd jmb\n\
            mtb: fbq dcs\n\
            hjp: zjr brf hlt rdr\n\
            nbc: jqb pzm\n\
            kkb: kpn khq szp fqr\n\
            fhg: gjk cbd nlr lnb\n\
            ltv: vlq zlq bzn\n\
            pnz: xsf hkr dfr\n\
            pqx: svh qtg\n\
            vtr: jrx jvb gfc spl\n\
            vzn: ssf\n\
            sxq: pcr pcm\n\
            zzx: qqr xhh spd\n\
            zsh: pbk rzb tnf hbl\n\
            sqp: jhq bkj tqh\n\
            fjd: ftg hgz glv jqb\n\
            kbz: zmr fdf xcg pcm\n\
            tqr: grd trg mkl zfq\n\
            zvd: gzv mlh bxp blg\n\
            zjm: xqc dsp gdg chr\n\
            ssc: nnm tlz cvc vpq\n\
            phd: fqn zqq\n\
            vff: srp krq\n\
            vqm: rln snd cfj\n\
            qqh: lrc chc tpf sjq\n\
            lkf: dlz fbt pfd\n\
            mph: zkq vjs\n\
            dbx: zvl pfb fnk brf\n\
            vbm: jkg xkh mzt\n\
            hcn: xxz nxt\n\
            fxd: rdd dts\n\
            dbj: mgl sqz mzq xgm jfc\n\
            dhl: qmp\n\
            tjg: jjr msr sjk\n\
            krz: bzm ljz gzz\n\
            dnj: zdc skf\n\
            gng: fkn jhj jkg\n\
            bzl: pzv gzl kjl\n\
            hjv: dlt xqk lnp\n\
            rjb: njv xtb qmr mvf\n\
            lhr: gpq\n\
            prc: ssf jdj\n\
            tsv: mlm\n\
            jdn: xlc dhk ckq ctf xtk\n\
            spz: dkg rkb\n\
            tfv: vkg\n\
            ssr: qpg vsq nmn zml rmm\n\
            ssl: sbl jrc ljt\n\
            nxz: jgp tlt ffd zxf\n\
            jvb: jqb\n\
            ftm: gfb\n\
            mtp: gfb gqt stt\n\
            zfj: xfv\n\
            xth: tvt ssq fpg\n\
            tfb: gcz\n\
            lzb: knh\n\
            xmj: lxx\n\
            dhf: dvd vns drz bdj\n\
            hnz: lpq\n\
            khz: gmk tcn pqg msr hgz tkx\n\
            nnx: hmz hjz pgh lfj\n\
            fnx: pcr jkh tfd vqv\n\
            blv: qrc mmk\n\
            ccb: mkj smc shq zpd srl psx\n\
            mcz: mbj ljn gjp bkf kkj nsf\n\
            ldd: rgf rhf srr vxc cjm\n\
            lbg: brg gsv xhm dkt pbx\n\
            ccl: dgp hrp rxj\n\
            dhk: xdb\n\
            cdv: kqb ksx rqv\n\
            brc: qfm dcj tkz dgp skb\n\
            qqb: nvr vxz qdf\n\
            kks: hbq jhq xld pvf\n\
            xtv: kfl sbm fvl xnl\n\
            zmq: fmh nrr zdb\n\
            pfp: lfj xjr\n\
            qls: cgd ghz pnl\n\
            jrr: tll bpt kcg\n\
            qlh: cfc cdl zrf\n\
            qbt: ngd dcl zhl\n\
            tht: mhg jhz pbq nfd\n\
            rjn: kmz lvg pbq rgn\n\
            tzm: jrm mzs\n\
            jxr: mzs jdf ssn skf\n\
            smm: bhj kcp mzq njv\n\
            fqf: fhq bqf tln sbg zng\n\
            fqs: dxg skp\n\
            mjn: xnx kcg bgl\n\
            cbt: vpb mfv cvl ccl\n\
            ksx: nbq\n\
            fnm: nmm ksm\n\
            vpb: zjx lkv tfd rqp pdb\n\
            prp: vtz flh hbk\n\
            jpd: kzg qxt kqb ztd\n\
            pzg: bkj pkp\n\
            jlj: psz rkq psc lqb\n\
            rxk: jvd lqr shr jql rrb llg mdb\n\
            lmv: mjn qfd bsj bvm\n\
            pzv: szt\n\
            dfr: mqx vls\n\
            lbt: prc nlq lsl\n\
            msc: smd tkz\n\
            qxm: pgt zzd fsg\n\
            bkf: cqd fnk\n\
            txf: ggj ggr lkv jpp\n\
            sfr: qbq fdt qxt\n\
            smc: gqf rjz\n\
            tmq: sgs pkp\n\
            fmt: qqq fdt\n\
            vbk: lcj ztm\n\
            spv: jms vfz jvc zdm\n\
            xzj: dkl vkr bll vtg ppz\n\
            llg: pdh frd ljd\n\
            xzm: kkj blt zdm hnv\n\
            ktq: mqs mhg cts\n\
            rxs: drn xmb tfv\n\
            mpt: hnz\n\
            tcn: gdh\n\
            tsj: xrn ndv msr\n\
            nfj: msc nkl\n\
            ndh: fqn tcq\n\
            ndb: zlc dkg sbl jdz\n\
            rrs: vzr\n\
            lbb: mlc\n\
            lpl: zpl llf\n\
            xqc: psf pkp\n\
            mrx: bqt hqh gzr fbc frh\n\
            chq: sht qkk vfz pqn\n\
            thh: gzp xxs vbm\n\
            ksj: ndr rnk ttk jqf\n\
            tbn: gnf xnx mjn\n\
            qfj: rmr hjr jqk ntb hbk\n\
            zpm: pzk\n\
            dgn: cfc\n\
            jvk: scc qzt pcm\n\
            ctd: dnn vdn gxp fzf jdx\n\
            ghc: sdf lxr\n\
            bpf: tjf lvp blj ttm\n\
            tfd: mmk rrs\n\
            mmq: jfv\n\
            qcp: tdm xzp vpp\n\
            bmf: xzk mmq xgr\n\
            jmc: tzk jjr rpm";

        let answer = solve(input).unwrap();

        assert_eq!(592171, answer);
    }
}
