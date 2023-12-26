// Advent of Code 2023 Day 25 solution
//
// Stoer-Wagner algorithm over graphs with constant weight 1
// https://www.cs.dartmouth.edu/~ac/Teach/CS105-Winter05/Handouts/stoerwagner-mincut.pdf
use std::io;
use std::io::prelude::*;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Debug)]
struct Graph<T: Clone + Eq + std::hash::Hash> {
    pub vertices: HashSet<T>,
    pub edges: HashMap<(T, T), usize>,
}

impl<T: Clone + Eq + std::hash::Hash> Graph<T> {
    fn from_adjacency_list<I: std::iter::IntoIterator<Item = ((T, T), usize)>>(adjacency_list: I) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashMap::new(),
        };

        adjacency_list.into_iter().for_each(|((u, v), _w)| {
            g.vertices.insert(u.clone());
            g.vertices.insert(v.clone());
            g.edges.insert((u, v), 1);
        });

        g
    }

    fn most_tightly_connected(&self, scanned_vertices: HashSet<T>) -> Option<T> {
        self.vertices.difference(&scanned_vertices).max_by_key(|v| {
            self.edges
                .iter()
                .filter(|e| (e.0.0 == **v && scanned_vertices.contains(&e.0.1)) || (e.0.1 == **v && scanned_vertices.contains(&e.0.0)))
                .collect::<Vec<(&(T, T), &usize)>>().len()
        }).cloned()
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

        g.vertices.insert(u);
        vs.split(" ").for_each(|v| {
            g.vertices.insert(v);
            g.edges.insert((u, v), 1);
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

    const TEST_GRAPH_VERTEX_COUNT: usize = 5;

    impl quickcheck::Arbitrary for Graph<usize> {
        fn arbitrary(gen: &mut quickcheck::Gen) -> Graph<usize> {
            Graph::from_adjacency_list((0..TEST_GRAPH_VERTEX_COUNT)
                .map(|i| (i, (0..TEST_GRAPH_VERTEX_COUNT).map(|j| i != j && bool::arbitrary(gen)).collect::<Vec<bool>>()))
                .flat_map(|(i, neighbours)| {
                    neighbours
                        .iter()
                        .enumerate()
                        .filter(|adjacency| *adjacency.1)
                        .map(|adjacency| ((i, adjacency.0), 1))
                        .collect::<Vec<((usize, usize), usize)>>()
                })
                .collect::<Vec<((usize, usize), usize)>>())
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
            "bvb","cmg","frs","hfx",
            "jqt","lhk","lsr","ntq",
            "nvd","pzl","qnr","rhn",
            "rsh","rzs","xhk"
        ]);
        let expected_edges = HashMap::from_iter([
            (("jqt", "rhn"), 1),
            (("jqt", "xhk"), 1),
            (("jqt", "nvd"), 1),
            (("rsh", "frs"), 1),
            (("rsh", "pzl"), 1),
            (("rsh", "lsr"), 1),
            (("xhk", "hfx"), 1),
            (("cmg", "qnr"), 1),
            (("cmg", "nvd"), 1),
            (("cmg", "lhk"), 1),
            (("cmg", "bvb"), 1),
            (("rhn", "xhk"), 1),
            (("rhn", "bvb"), 1),
            (("rhn", "hfx"), 1),
            (("bvb", "xhk"), 1),
            (("bvb", "hfx"), 1),
            (("pzl", "lsr"), 1),
            (("pzl", "hfx"), 1),
            (("pzl", "nvd"), 1),
            (("qnr", "nvd"), 1),
            (("ntq", "jqt"), 1),
            (("ntq", "hfx"), 1),
            (("ntq", "bvb"), 1),
            (("ntq", "xhk"), 1),
            (("nvd", "lhk"), 1),
            (("lsr", "lhk"), 1),
            (("rzs", "qnr"), 1),
            (("rzs", "cmg"), 1),
            (("rzs", "lsr"), 1),
            (("rzs", "rsh"), 1),
            (("frs", "qnr"), 1),
            (("frs", "lhk"), 1),
            (("frs", "lsr"), 1),
        ]);

        let g = parse_input(input).unwrap();
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(expected_edges, g.edges);
    }

    #[test]
    fn graphs_constructible_from_adjacency_lists() {
        let adjacency_list = HashMap::from_iter([
            (("jqt", "rhn"), 1),
            (("jqt", "xhk"), 1),
            (("jqt", "nvd"), 1),
            (("rsh", "frs"), 1),
            (("rsh", "pzl"), 1),
            (("rsh", "lsr"), 1),
            (("xhk", "hfx"), 1),
            (("cmg", "qnr"), 1),
            (("cmg", "nvd"), 1),
            (("cmg", "lhk"), 1),
            (("cmg", "bvb"), 1),
            (("rhn", "xhk"), 1),
            (("rhn", "bvb"), 1),
            (("rhn", "hfx"), 1),
            (("bvb", "xhk"), 1),
            (("bvb", "hfx"), 1),
            (("pzl", "lsr"), 1),
            (("pzl", "hfx"), 1),
            (("pzl", "nvd"), 1),
            (("qnr", "nvd"), 1),
            (("ntq", "jqt"), 1),
            (("ntq", "hfx"), 1),
            (("ntq", "bvb"), 1),
            (("ntq", "xhk"), 1),
            (("nvd", "lhk"), 1),
            (("lsr", "lhk"), 1),
            (("rzs", "qnr"), 1),
            (("rzs", "cmg"), 1),
            (("rzs", "lsr"), 1),
            (("rzs", "rsh"), 1),
            (("frs", "qnr"), 1),
            (("frs", "lhk"), 1),
            (("frs", "lsr"), 1),
        ]);
        let expected_vertices = HashSet::from_iter([
            "bvb","cmg","frs","hfx",
            "jqt","lhk","lsr","ntq",
            "nvd","pzl","qnr","rhn",
            "rsh","rzs","xhk"
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
        let mut dc = g.edges.iter().fold(HashMap::<usize, usize>::new(), |mut h, ((u, v), _w)| {
            if !was_scanned[*u] && was_scanned[*v] {
                match h.get(u) {
                    None => { h.insert(*u, 1) }
                    Some(n) => { h.insert(*u, n + 1) }
                };
            } else if was_scanned[*u] && !was_scanned[*v] {
                match h.get(v) {
                    None => { h.insert(*v, 1) }
                    Some(n) => { h.insert(*v, n + 1) }
                };
            }
            h
        });
        if dc.len() == 0 {
            return quickcheck::TestResult::discard();
        }
        let scanned_vertices = was_scanned.iter().enumerate().filter(|(v, scanned)| **scanned).map(|p| p.0).collect::<HashSet<usize>>();

        let v = g.most_tightly_connected(scanned_vertices.clone()).unwrap();
        let expected_vertex = dc.iter().max_by_key(|kv| kv.1).unwrap().0;

        assert!(dc.iter().all(|(_v, degree)| *degree <= *dc.get(&v).unwrap_or(&0)), "expected {:?}, got {:?} with visited vertices {:?}", expected_vertex, v, scanned_vertices);

        quickcheck::TestResult::passed()
    }

    #[quickcheck]
    fn graph_can_merge_two_vertices(g: Graph<usize>, u: usize, v: usize) -> quickcheck::TestResult {
        if u >= TEST_GRAPH_VERTEX_COUNT || v >= TEST_GRAPH_VERTEX_COUNT {
            return quickcheck::TestResult::discard();
        }

        quickcheck::TestResult::passed()
    }
}
