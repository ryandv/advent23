// Advent of Code 2023 Day 25 solution
//
// Stoer-Wagner algorithm over graphs with constant weight 1
// https://www.cs.dartmouth.edu/~ac/Teach/CS105-Winter05/Handouts/stoerwagner-mincut.pdf
use std::io;
use std::io::prelude::*;
use std::collections::HashSet;

struct Graph<T: Eq> {
    pub vertices: HashSet<T>,
    pub edges: HashSet<(T, T)>,
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
}
