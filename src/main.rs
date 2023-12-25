// Advent of Code 2023 Day 25 solution
//
// Stoer-Wagner algorithm over graphs with constant weight 1
// https://www.cs.dartmouth.edu/~ac/Teach/CS105-Winter05/Handouts/stoerwagner-mincut.pdf
use std::io;
use std::io::prelude::*;
use std::collections::HashSet;

#[derive(Clone)]
struct Graph<T: Clone + Eq + std::hash::Hash> {
    pub vertices: HashSet<T>,
    pub edges: HashSet<(T, T)>,
}

impl<T: Clone + Eq + std::hash::Hash> Graph<T> {
    fn from_adjacency_list<I: std::iter::IntoIterator<Item = (T, T)>>(adjacency_list: I) -> Graph<T> {
        let mut g = Graph {
            vertices: HashSet::new(),
            edges: HashSet::new(),
        };

        adjacency_list.into_iter().for_each(|(u, v)| {
            g.vertices.insert(u.clone());
            g.vertices.insert(v.clone());
            g.edges.insert((u, v));
        });

        g
    }
}

fn main() -> io::Result<()> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;

    Ok(())
}

fn parse_input(input: &str) -> Result<Graph<&str>, &str> {
    input.lines().try_fold(Graph { vertices: HashSet::new(), edges: HashSet:: new() }, |mut g, ln| -> Result<Graph<&str>, &str> {
        let (u, vs) = ln.split_once(": ").ok_or("missing colon delimiter")?;

        g.vertices.insert(u);
        vs.split(" ").for_each(|v| {
            g.vertices.insert(v);
            g.edges.insert((u, v));
        });

        Ok(g)
    })
}

#[cfg(test)]
mod test {
    use super::*;

    // test on graphs with 20 vertices
    impl quickcheck::Arbitrary for Graph<usize> {
        fn arbitrary(gen: &mut quickcheck::Gen) -> Graph<usize> {
            Graph::from_adjacency_list((0..20)
                .map(|i| (i, (0..20).map(|_| bool::arbitrary(gen)).collect::<Vec<bool>>()))
                .flat_map(|(i, neighbours)| {
                    neighbours
                        .iter()
                        .enumerate()
                        .filter(|adjacency| *adjacency.1)
                        .map(|adjacency| (i, adjacency.0))
                        .collect::<Vec<(usize, usize)>>()
                })
                .collect::<Vec<(usize, usize)>>())
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
        let expected_edges = HashSet::<(&str, &str)>::from_iter([
            ("jqt", "rhn"),
            ("jqt", "xhk"),
            ("jqt", "nvd"),
            ("rsh", "frs"),
            ("rsh", "pzl"),
            ("rsh", "lsr"),
            ("xhk", "hfx"),
            ("cmg", "qnr"),
            ("cmg", "nvd"),
            ("cmg", "lhk"),
            ("cmg", "bvb"),
            ("rhn", "xhk"),
            ("rhn", "bvb"),
            ("rhn", "hfx"),
            ("bvb", "xhk"),
            ("bvb", "hfx"),
            ("pzl", "lsr"),
            ("pzl", "hfx"),
            ("pzl", "nvd"),
            ("qnr", "nvd"),
            ("ntq", "jqt"),
            ("ntq", "hfx"),
            ("ntq", "bvb"),
            ("ntq", "xhk"),
            ("nvd", "lhk"),
            ("lsr", "lhk"),
            ("rzs", "qnr"),
            ("rzs", "cmg"),
            ("rzs", "lsr"),
            ("rzs", "rsh"),
            ("frs", "qnr"),
            ("frs", "lhk"),
            ("frs", "lsr"),
        ]);

        let g = parse_input(input).unwrap();
        assert_eq!(expected_vertices, g.vertices);
        assert_eq!(expected_edges, g.edges);
    }

    #[test]
    fn graphs_constructible_from_adjacency_lists() {
        let adjacency_list = HashSet::<(&str, &str)>::from_iter([
            ("jqt", "rhn"),
            ("jqt", "xhk"),
            ("jqt", "nvd"),
            ("rsh", "frs"),
            ("rsh", "pzl"),
            ("rsh", "lsr"),
            ("xhk", "hfx"),
            ("cmg", "qnr"),
            ("cmg", "nvd"),
            ("cmg", "lhk"),
            ("cmg", "bvb"),
            ("rhn", "xhk"),
            ("rhn", "bvb"),
            ("rhn", "hfx"),
            ("bvb", "xhk"),
            ("bvb", "hfx"),
            ("pzl", "lsr"),
            ("pzl", "hfx"),
            ("pzl", "nvd"),
            ("qnr", "nvd"),
            ("ntq", "jqt"),
            ("ntq", "hfx"),
            ("ntq", "bvb"),
            ("ntq", "xhk"),
            ("nvd", "lhk"),
            ("lsr", "lhk"),
            ("rzs", "qnr"),
            ("rzs", "cmg"),
            ("rzs", "lsr"),
            ("rzs", "rsh"),
            ("frs", "qnr"),
            ("frs", "lhk"),
            ("frs", "lsr"),
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
}
