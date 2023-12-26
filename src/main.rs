// Advent of Code 2023 Day 25 solution
//
// Stoer-Wagner algorithm over graphs with constant weight 1
// https://www.cs.dartmouth.edu/~ac/Teach/CS105-Winter05/Handouts/stoerwagner-mincut.pdf
use std::io;
use std::io::prelude::*;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Debug)]
struct Graph<T: Clone + Eq + Ord + std::hash::Hash> {
    pub vertices: HashSet<BTreeSet<T>>,
    pub edges: HashMap<UnorderedPair<BTreeSet<T>>, usize>, // TODO: consider an Rc or something here..
}

impl<T: Clone + Eq + Ord + std::hash::Hash> Graph<T> {
    fn from_adjacency_list<I: std::iter::IntoIterator<Item = (UnorderedPair<BTreeSet<T>>, usize)>>(adjacency_list: I) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashMap::new(),
        };

        adjacency_list.into_iter().for_each(|(UnorderedPair((u, v)), _w)| {
            g.vertices.insert(u.clone());
            g.vertices.insert(v.clone());
            g.edges.insert(UnorderedPair((u, v)), 1);
        });

        g
    }

    fn most_tightly_connected(&self, scanned_vertices: HashSet<BTreeSet<T>>) -> Option<BTreeSet<T>> {
        self.vertices.difference(&scanned_vertices).max_by_key(|v| {
            self.edges
                .iter()
                .filter(|(UnorderedPair(e), _w)| (**v == e.0 && scanned_vertices.contains(&e.1)) || (**v == e.1 && scanned_vertices.contains(&e.0)))
                .collect::<Vec<(&UnorderedPair<BTreeSet<T>>, &usize)>>().len()
        }).cloned()
    }

    fn merge(&self, u: &BTreeSet<T>, v: &BTreeSet<T>) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashMap::<UnorderedPair<BTreeSet<T>>, usize>::new(),
        };

        self.vertices.iter().for_each(|x| {
            if x != u && x != v {
                g.vertices.insert(x.clone());
            }
        });
        self.edges.iter().for_each(|(e@UnorderedPair((s, t)), w)| {
            if *e != UnorderedPair((u.clone(), v.clone())) {
                if e.contains(&u) {
                    let x = e.partner(&u);
                    let w0 = w + self.edges.get(&UnorderedPair((x.clone(), v.clone()))).unwrap_or(&0);
                    g.edges.insert(UnorderedPair((u | v, x.clone())), w0);
                } else if e.contains(&v) {
                    let x = e.partner(&v);
                    let w0 = w + self.edges.get(&UnorderedPair((x.clone(), u.clone()))).unwrap_or(&0);
                    g.edges.insert(UnorderedPair((u | v, x.clone())), w0);
                } else {
                    g.edges.insert(UnorderedPair((s.clone(), t.clone())), *w);
                }
            }
        });
        g.vertices.insert(u | v);

        g
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

impl<T: std::hash::Hash + Ord> std::hash::Hash for UnorderedPair<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
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

        g.vertices.insert(BTreeSet::from_iter([u]));
        vs.split(" ").for_each(|v| {
            g.vertices.insert(BTreeSet::from_iter([v]));
            g.edges.insert(UnorderedPair((BTreeSet::from_iter([u]), BTreeSet::from_iter([v]))), 1);
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
    use super::*;

    const TEST_GRAPH_VERTEX_COUNT: usize = 3;

    impl quickcheck::Arbitrary for Graph<usize> {
        fn arbitrary(gen: &mut quickcheck::Gen) -> Graph<usize> {
            Graph::from_adjacency_list((0..TEST_GRAPH_VERTEX_COUNT)
                .map(|i| (i, (0..TEST_GRAPH_VERTEX_COUNT).map(|j| i != j && bool::arbitrary(gen)).collect::<Vec<bool>>()))
                .flat_map(|(i, neighbours)| {
                    neighbours
                        .iter()
                        .enumerate()
                        .filter(|adjacency| *adjacency.1)
                        .map(|adjacency| (UnorderedPair((BTreeSet::from_iter([i]), BTreeSet::from_iter([adjacency.0]))), 1))
                        .collect::<Vec<(UnorderedPair<BTreeSet<usize>>, usize)>>()
                })
                .collect::<Vec<(UnorderedPair<BTreeSet<usize>>, usize)>>())
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
            BTreeSet::from_iter(["bvb"]),BTreeSet::from_iter(["cmg"]),BTreeSet::from_iter(["frs"]),BTreeSet::from_iter(["hfx"]),
            BTreeSet::from_iter(["jqt"]),BTreeSet::from_iter(["lhk"]),BTreeSet::from_iter(["lsr"]),BTreeSet::from_iter(["ntq"]),
            BTreeSet::from_iter(["nvd"]),BTreeSet::from_iter(["pzl"]),BTreeSet::from_iter(["qnr"]),BTreeSet::from_iter(["rhn"]),
            BTreeSet::from_iter(["rsh"]),BTreeSet::from_iter(["rzs"]),BTreeSet::from_iter(["xhk"])
        ]);
        let expected_edges = HashMap::from_iter([
            (UnorderedPair((BTreeSet::from_iter(["jqt"]), BTreeSet::from_iter(["rhn"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["jqt"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["jqt"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rsh"]), BTreeSet::from_iter(["frs"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rsh"]), BTreeSet::from_iter(["pzl"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rsh"]), BTreeSet::from_iter(["lsr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["xhk"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["qnr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["bvb"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rhn"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rhn"]), BTreeSet::from_iter(["bvb"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rhn"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["bvb"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["bvb"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["pzl"]), BTreeSet::from_iter(["lsr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["pzl"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["pzl"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["qnr"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["jqt"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["bvb"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["nvd"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["lsr"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["qnr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["cmg"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["lsr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["rsh"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["frs"]), BTreeSet::from_iter(["qnr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["frs"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["frs"]), BTreeSet::from_iter(["lsr"]))), 1),
        ]);

        let g = parse_input(input).unwrap();
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(expected_edges, g.edges);
    }

    #[test]
    fn graphs_constructible_from_adjacency_lists() {
        let adjacency_list = HashMap::from_iter([
            (UnorderedPair((BTreeSet::from_iter(["jqt"]), BTreeSet::from_iter(["rhn"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["jqt"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["jqt"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rsh"]), BTreeSet::from_iter(["frs"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rsh"]), BTreeSet::from_iter(["pzl"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rsh"]), BTreeSet::from_iter(["lsr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["xhk"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["qnr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["cmg"]), BTreeSet::from_iter(["bvb"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rhn"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rhn"]), BTreeSet::from_iter(["bvb"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rhn"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["bvb"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["bvb"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["pzl"]), BTreeSet::from_iter(["lsr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["pzl"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["pzl"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["qnr"]), BTreeSet::from_iter(["nvd"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["jqt"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["hfx"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["bvb"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["ntq"]), BTreeSet::from_iter(["xhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["nvd"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["lsr"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["qnr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["cmg"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["lsr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["rzs"]), BTreeSet::from_iter(["rsh"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["frs"]), BTreeSet::from_iter(["qnr"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["frs"]), BTreeSet::from_iter(["lhk"]))), 1),
            (UnorderedPair((BTreeSet::from_iter(["frs"]), BTreeSet::from_iter(["lsr"]))), 1),
        ]);
        let expected_vertices = HashSet::from_iter([
            BTreeSet::from_iter(["bvb"]),BTreeSet::from_iter(["cmg"]),BTreeSet::from_iter(["frs"]),BTreeSet::from_iter(["hfx"]),
            BTreeSet::from_iter(["jqt"]),BTreeSet::from_iter(["lhk"]),BTreeSet::from_iter(["lsr"]),BTreeSet::from_iter(["ntq"]),
            BTreeSet::from_iter(["nvd"]),BTreeSet::from_iter(["pzl"]),BTreeSet::from_iter(["qnr"]),BTreeSet::from_iter(["rhn"]),
            BTreeSet::from_iter(["rsh"]),BTreeSet::from_iter(["rzs"]),BTreeSet::from_iter(["xhk"])
        ]);

        let g = Graph::from_adjacency_list(adjacency_list.clone());
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(adjacency_list, g.edges);
    }

    #[quickcheck]
    fn finds_most_tightly_connected_vertex(g: Graph<usize>, previously_scanned: SubsetVector) -> quickcheck::TestResult {
        if g.edges.len() == 0 {
            return quickcheck::TestResult::discard();
        }

        let SubsetVector(was_scanned) = previously_scanned;
        let mut dc = g.edges.iter().fold(HashMap::<BTreeSet<usize>, usize>::new(), |mut h, (UnorderedPair((u, v)), _w)| {
            // all vertices are singleton sets by construction
            if !was_scanned[*u.first().unwrap()] && was_scanned[*v.first().unwrap()] {
                match h.get(u) {
                    None => { h.insert(u.clone(), 1) }
                    Some(n) => { h.insert(u.clone(), n + 1) }
                };
            } else if was_scanned[*u.first().unwrap()] && !was_scanned[*v.first().unwrap()] {
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
        let scanned_vertices = was_scanned.iter().enumerate().filter(|(v, scanned)| **scanned).map(|p| BTreeSet::from_iter([p.0])).collect::<HashSet<BTreeSet<usize>>>();

        let v = g.most_tightly_connected(scanned_vertices.clone()).unwrap();
        let expected_vertex = dc.iter().max_by_key(|kv| kv.1).unwrap().0;

        assert!(dc.iter().all(|(_v, degree)| *degree <= *dc.get(&v).unwrap_or(&0)), "expected {:?}, got {:?} with visited vertices {:?}", expected_vertex, v, scanned_vertices);

        quickcheck::TestResult::passed()
    }

    #[quickcheck]
    fn graph_can_merge_two_vertices(g: Graph<usize>, nu: usize, nv: usize) -> quickcheck::TestResult {
        if nu >= TEST_GRAPH_VERTEX_COUNT || nv >= TEST_GRAPH_VERTEX_COUNT || nu == nv {
            return quickcheck::TestResult::discard();
        }
        let u = BTreeSet::from_iter([nu]);
        let v = BTreeSet::from_iter([nv]);
        let expected_merge = &u | &v;
        let mut merged_edges: Vec<(BTreeSet<usize>, &UnorderedPair<BTreeSet<usize>>)> = g.vertices
            .iter()
            .filter(|x| g.edges.contains_key(&UnorderedPair((x.clone().clone(), u.clone()))) && g.edges.contains_key(&UnorderedPair((x.clone().clone(), v.clone()))))
            .flat_map(|x| g.edges
                .iter()
                .filter(|(e, _w)| **e == UnorderedPair((x.clone(), u.clone())) || **e == UnorderedPair((x.clone(), v.clone())))
                .map(|(e, w)| (x.clone(), e)))
            .collect();
        let mut adopted_edges: Vec<(BTreeSet<usize>, &UnorderedPair<BTreeSet<usize>>)> = g.vertices
            .difference(&HashSet::from_iter(expected_merge.clone().iter().map(|x| BTreeSet::from_iter([*x]))))
            .filter(|x| g.edges.contains_key(&UnorderedPair((x.clone().clone(), u.clone()))) ^ g.edges.contains_key(&UnorderedPair((x.clone().clone(), v.clone()))))
            .flat_map(|x| g.edges
                .iter()
                .filter(|(e, _w)| **e == UnorderedPair((x.clone(), u.clone())) || **e == UnorderedPair((x.clone(), v.clone())))
                .map(|(e, w)| (x.clone(), e)))
            .collect();

        let g0 = g.merge(&u, &v);
        let old_vertices = BTreeSet::from_iter(g.vertices.clone());
        let remaining_vertices: HashSet<BTreeSet<usize>> = old_vertices.difference(&BTreeSet::from_iter([u.clone(), v.clone()])).map(|x| x.clone()).collect();

        assert!(!g0.vertices.contains(&u), "expected {:?} to not contain {:?}", g0.vertices, u);
        assert!(!g0.vertices.contains(&v), "expected {:?} to not contain {:?}", g0.vertices, v);
        assert!(g0.vertices.contains(&expected_merge));
        assert!(remaining_vertices.iter().all(|x| g0.vertices.contains(x)), "expected {:?} to contain {:?}", g0.vertices, remaining_vertices);
        assert!(!g0.edges.contains_key(&UnorderedPair((u.clone(), v.clone()))), "expected {:?} to not contain edge {:?}", g0.edges, UnorderedPair((BTreeSet::from_iter([u.clone()]), BTreeSet::from_iter([v.clone()]))));
        assert!(merged_edges.iter().all(|(x, UnorderedPair((s, t)))| !g0.edges.contains_key(&UnorderedPair((s.clone(), t.clone())))), "expected {:?} to not contain unmerged edges from {:?}", g0.edges, merged_edges);
        assert!(merged_edges.iter().all(|(x, _e)| g0.edges.get(&UnorderedPair((x.clone(), &u | &v))) == Some(&2)), "expected {:?} to contain merged edges from {:?}", g0.edges, merged_edges);
        assert!(adopted_edges.iter().all(|(x, _e)| g0.edges.get(&UnorderedPair((x.clone(), &u | &v))) == Some(&1)), "expected {:?} to contain adopted edges from {:?}", g0.edges, adopted_edges);
        quickcheck::TestResult::passed()
    }
}
