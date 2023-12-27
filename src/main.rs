// Advent of Code 2023 Day 25 solution
//
// Stoer-Wagner algorithm over graphs with constant weight 1
// https://www.cs.dartmouth.edu/~ac/Teach/CS105-Winter05/Handouts/stoerwagner-mincut.pdf

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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Ord, PartialOrd)]
struct Edge<T: Clone + Eq + Ord + Hash>(UnorderedPair<Vertex<T>>);

impl<T: Clone + Eq + Ord + Hash> Edge<T> {
    pub fn new(u: Vertex<T>, v: Vertex<T>) -> Edge<T> {
        Edge(UnorderedPair((u, v)))
    }

    pub fn partner(&self, v: &Vertex<T>) -> &Vertex<T> {
        self.0.partner(v)
    }

    pub fn joins(&self, v: &Vertex<T>) -> bool {
        self.0.contains(v)
    }

}

impl<T: Clone + Eq + Ord + Hash> Graph<T> {
    pub fn from_adjacency_lists<I: std::iter::IntoIterator<Item = (Edge<T>, usize)>>(adjacency_list: I) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashMap::new(),
        };

        adjacency_list.into_iter().for_each(|(Edge(UnorderedPair((u, v))), _w)| {
            g.vertices.insert(u.clone());
            g.vertices.insert(v.clone());
            g.edges.insert(Edge::new(u, v), 1);
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
        self.edges.iter().for_each(|(e@Edge(UnorderedPair((s, t))), w)| {
            if *e != Edge::new(u.clone(), v.clone()) {
                if e.joins(&u) {
                    let x = e.partner(&u);
                    let w0 = w + self.edges.get(&Edge::new(x.clone(), v.clone())).unwrap_or(&0);
                    g.edges.insert(Edge::new(u.merge(v), x.clone()), w0);
                } else if e.joins(&v) {
                    let x = e.partner(&v);
                    let w0 = w + self.edges.get(&Edge::new(x.clone(), u.clone())).unwrap_or(&0);
                    g.edges.insert(Edge::new(u.merge(v), x.clone()), w0);
                } else {
                    g.edges.insert(Edge::new(s.clone(), t.clone()), *w);
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

fn main() -> io::Result<()> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;

    Ok(())
}

fn parse_input(input: &str) -> Result<Graph<&str>, &str> {
    input.lines().try_fold(Graph { vertices: HashSet::new(), edges: HashMap::new() }, |mut g, ln| -> Result<Graph<&str>, &str> {
        let (u, vs) = ln.split_once(": ").ok_or("missing colon delimiter")?;

        g.vertices.insert(Vertex::new(u));
        vs.split(" ").for_each(|v| {
            g.vertices.insert(Vertex::new(v));
            g.edges.insert(Edge::new(Vertex::new(u), Vertex::new(v)), 1);
        });

        Ok(g)
    })
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

    const TEST_GRAPH_VERTEX_COUNT: usize = 50;

    impl quickcheck::Arbitrary for Graph<usize> {
        fn arbitrary(gen: &mut quickcheck::Gen) -> Graph<usize> {
            Graph::from_adjacency_lists((0..TEST_GRAPH_VERTEX_COUNT)
                .map(|i| (i, (0..TEST_GRAPH_VERTEX_COUNT).map(|j| i != j && bool::arbitrary(gen)).collect::<Vec<bool>>()))
                .flat_map(|(i, neighbours)| {
                    neighbours
                        .iter()
                        .enumerate()
                        .filter(|adjacency| *adjacency.1)
                        .map(|adjacency| (Edge::new(Vertex::new(i), Vertex::new(adjacency.0)), 1))
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
            (Edge::new(Vertex::new("jqt"), Vertex::new("rhn")), 1),
            (Edge::new(Vertex::new("jqt"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("jqt"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("rsh"), Vertex::new("frs")), 1),
            (Edge::new(Vertex::new("rsh"), Vertex::new("pzl")), 1),
            (Edge::new(Vertex::new("rsh"), Vertex::new("lsr")), 1),
            (Edge::new(Vertex::new("xhk"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("qnr")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("bvb")), 1),
            (Edge::new(Vertex::new("rhn"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("rhn"), Vertex::new("bvb")), 1),
            (Edge::new(Vertex::new("rhn"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("bvb"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("bvb"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("pzl"), Vertex::new("lsr")), 1),
            (Edge::new(Vertex::new("pzl"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("pzl"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("qnr"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("jqt")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("bvb")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("nvd"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("lsr"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("qnr")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("cmg")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("lsr")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("rsh")), 1),
            (Edge::new(Vertex::new("frs"), Vertex::new("qnr")), 1),
            (Edge::new(Vertex::new("frs"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("frs"), Vertex::new("lsr")), 1),
        ]);

        let g = parse_input(input).unwrap();
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(expected_edges, g.edges);
    }

    #[test]
    fn graphs_constructible_from_adjacency_lists() {
        let adjacency_list: HashMap<Edge<&str>, usize> = HashMap::from_iter([
            (Edge::new(Vertex::new("jqt"), Vertex::new("rhn")), 1),
            (Edge::new(Vertex::new("jqt"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("jqt"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("rsh"), Vertex::new("frs")), 1),
            (Edge::new(Vertex::new("rsh"), Vertex::new("pzl")), 1),
            (Edge::new(Vertex::new("rsh"), Vertex::new("lsr")), 1),
            (Edge::new(Vertex::new("xhk"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("qnr")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("cmg"), Vertex::new("bvb")), 1),
            (Edge::new(Vertex::new("rhn"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("rhn"), Vertex::new("bvb")), 1),
            (Edge::new(Vertex::new("rhn"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("bvb"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("bvb"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("pzl"), Vertex::new("lsr")), 1),
            (Edge::new(Vertex::new("pzl"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("pzl"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("qnr"), Vertex::new("nvd")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("jqt")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("hfx")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("bvb")), 1),
            (Edge::new(Vertex::new("ntq"), Vertex::new("xhk")), 1),
            (Edge::new(Vertex::new("nvd"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("lsr"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("qnr")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("cmg")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("lsr")), 1),
            (Edge::new(Vertex::new("rzs"), Vertex::new("rsh")), 1),
            (Edge::new(Vertex::new("frs"), Vertex::new("qnr")), 1),
            (Edge::new(Vertex::new("frs"), Vertex::new("lhk")), 1),
            (Edge::new(Vertex::new("frs"), Vertex::new("lsr")), 1),
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
                .filter(|(Edge(UnorderedPair(e)), _w)| (**v == e.0 && scanned_vertices.contains(&e.1)) || (**v == e.1 && scanned_vertices.contains(&e.0)))
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
        let mut dc = g.edges.iter().fold(HashMap::<Vertex<usize>, usize>::new(), |mut h, (Edge(UnorderedPair((u, v))), _w)| {
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
            .filter(|x| g.edges.contains_key(&Edge::new(x.clone().clone(), u.clone())) && g.edges.contains_key(&Edge::new(x.clone().clone(), v.clone())))
            .flat_map(|x| g.edges
                .iter()
                .filter(|(e, _w)| **e == Edge::new(x.clone(), u.clone()) || **e == Edge::new(x.clone(), v.clone()))
                .map(|(e, w)| (x.clone(), e)))
            .collect();
        let mut adopted_edges: Vec<(Vertex<usize>, &Edge<usize>)> = g.vertices
            .difference(&HashSet::from_iter(expected_merge.clone().into_iter().map(|x| Vertex::new(*x))))
            .filter(|x| g.edges.contains_key(&Edge::new(x.clone().clone(), u.clone())) ^ g.edges.contains_key(&Edge::new(x.clone().clone(), v.clone())))
            .flat_map(|x| g.edges
                .iter()
                .filter(|(e, _w)| **e == Edge::new(x.clone(), u.clone()) || **e == Edge::new(x.clone(), v.clone()))
                .map(|(e, w)| (x.clone(), e)))
            .collect();

        let g0 = g.merge(&u, &v);
        let old_vertices = BTreeSet::from_iter(g.vertices.clone());
        let remaining_vertices: HashSet<Vertex<usize>> = old_vertices.difference(&BTreeSet::from_iter([u.clone(), v.clone()])).map(|x| x.clone()).collect();

        assert!(!g0.vertices.contains(&u), "expected {:?} to not contain {:?}", g0.vertices, u);
        assert!(!g0.vertices.contains(&v), "expected {:?} to not contain {:?}", g0.vertices, v);
        assert!(g0.vertices.contains(&expected_merge));
        assert!(remaining_vertices.iter().all(|x| g0.vertices.contains(x)), "expected {:?} to contain {:?}", g0.vertices, remaining_vertices);
        assert!(!g0.edges.contains_key(&Edge::new(u.clone(), v.clone())), "expected {:?} to not contain edge {:?}", g0.edges, Edge::new(Vertex::new(u.clone()), Vertex::new(v.clone())));
        assert!(merged_edges.iter().all(|(x, e)| !g0.edges.contains_key(e)), "expected {:?} to not contain unmerged edges from {:?}", g0.edges, merged_edges);
        assert!(merged_edges.iter().all(|(x, _e)| g0.edges.get(&Edge::new(x.clone(), u.merge(&v))) == Some(&2)), "expected {:?} to contain merged edges from {:?}", g0.edges, merged_edges);
        assert!(adopted_edges.iter().all(|(x, _e)| g0.edges.get(&Edge::new(x.clone(), u.merge(&v))) == Some(&1)), "expected {:?} to contain adopted edges from {:?}", g0.edges, adopted_edges);
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

    /*
    #[quickcheck]
    fn stoer_wagner_finds_a_cut(g: Graph<usize>, i: usize) -> quickcheck::TestResult {
        if i >= TEST_GRAPH_VERTEX_COUNT {
            return quickcheck::TestResult::discard();
        }

        let cut: HashSet<UnorderedPair<Vertex<T>>> = g.stoer_wagner(i);
        quickcheck::TestResult::passed()
    }
    */
}
