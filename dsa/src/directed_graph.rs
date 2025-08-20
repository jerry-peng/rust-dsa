//! Directed-graph implementation using index pointers technique

use std::{
    cmp,
    collections::{BinaryHeap, HashMap, HashSet, VecDeque},
    mem,
};

#[derive(Debug, PartialEq)]
pub struct DirectedGraph {
    nodes: Vec<Node>,
    node_id_to_index: HashMap<String, usize>, // id, index
}

#[derive(Debug, PartialEq)]
pub struct Node {
    id: String,
    to_nodes: HashMap<String, usize>, // to_id, weight
    from_nodes: HashSet<String>,
}

#[derive(Debug)]
pub enum SearchType {
    DepthFirst,
    BreathFirst,
}

#[derive(Debug, PartialEq)]
pub struct DuplicateNodeErr;

#[derive(Debug, PartialEq)]
pub struct InvalidNodeErr;

impl DirectedGraph {
    pub fn new() -> DirectedGraph {
        DirectedGraph {
            nodes: Vec::new(),
            node_id_to_index: HashMap::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    pub fn add_node(&mut self, id: String) -> Result<(), DuplicateNodeErr> {
        if self.node_id_to_index.contains_key(&id) {
            Err(DuplicateNodeErr)
        } else {
            self.nodes.push(Node {
                id: id.clone(),
                to_nodes: HashMap::new(),
                from_nodes: HashSet::new(),
            });
            self.node_id_to_index.insert(id, self.nodes.len() - 1);
            Ok(())
        }
    }

    pub fn assign_edge(
        &mut self,
        from_id: String,
        to_id: String,
        weight: usize,
    ) -> Result<Option<usize>, InvalidNodeErr> {
        if let Some(from_index) = self.node_id_to_index.get(&from_id)
            && let Some(to_index) = self.node_id_to_index.get(&to_id)
        {
            match self.get_two_nodes_mut(*from_index, *to_index) {
                Some((from_node, to_node)) => {
                    let old_weight = from_node.to_nodes.insert(to_id, weight);
                    to_node.from_nodes.insert(from_id);
                    Ok(old_weight)
                }
                None => Err(InvalidNodeErr),
            }
        } else {
            Err(InvalidNodeErr)
        }
    }

    pub fn get_node(&self, id: &str) -> Option<&Node> {
        if let Some(index) = self.node_id_to_index.get(id) {
            Some(&self.nodes[*index])
        } else {
            None
        }
    }

    pub fn get_edge_weight(&self, from_id: &str, to_id: &str) -> Option<&usize> {
        if let Some(from_index) = self.node_id_to_index.get(from_id) {
            let from_node = &self.nodes[*from_index];
            from_node.to_nodes.get(to_id)
        } else {
            None
        }
    }

    pub fn remove_node(&mut self, id: &str) -> bool {
        match self.node_id_to_index.get_mut(id) {
            Some(index) => {
                let index = *index;
                self.detach_node_unchecked(index);
                if index < self.nodes.len() - 1 {
                    let id = &self.nodes.last().unwrap().id;
                    self.node_id_to_index.insert(id.to_string(), index);
                }
                self.nodes.swap_remove(index);
                self.node_id_to_index.remove(id);
                true
            }
            None => false,
        }
    }

    pub fn remove_edge(&mut self, from_id: &str, to_id: &str) -> Option<usize> {
        if let Some(from_index) = self.node_id_to_index.get(from_id)
            && let Some(to_index) = self.node_id_to_index.get(to_id)
        {
            match self.get_two_nodes_mut(*from_index, *to_index) {
                Some((from_node, to_node)) => {
                    let weight = from_node.to_nodes.remove(to_id);
                    if weight.is_some() {
                        to_node.from_nodes.remove(from_id);
                    }
                    weight
                }
                None => None,
            }
        } else {
            None
        }
    }

    fn get_two_nodes_mut(
        &mut self,
        from_index: usize,
        to_index: usize,
    ) -> Option<(&mut Node, &mut Node)> {
        // TODO assert indices are different?
        let small_index = cmp::min(from_index, to_index);
        let large_index = cmp::max(from_index, to_index);
        // cannot have multiple mutable reference into different items. Must use split_at_mut
        let (lower_slice, upper_slice) = self.nodes.split_at_mut(large_index);

        let (from_node, to_node) = match from_index.cmp(&to_index) {
            cmp::Ordering::Less => (&mut lower_slice[small_index], &mut upper_slice[0]),
            cmp::Ordering::Equal => return None,
            cmp::Ordering::Greater => (&mut upper_slice[0], &mut lower_slice[small_index]),
        };
        Some((from_node, to_node))
    }

    pub fn detach_node(&mut self, id: &str) -> bool {
        match self.node_id_to_index.get(id) {
            Some(index) => {
                self.detach_node_unchecked(*index);
                true
            }
            None => false,
        }
    }

    fn detach_node_unchecked(&mut self, index: usize) {
        // split 3 part, lower slice, node at index, and upperslice
        let (lower_slice, upper_slice) = self.nodes.split_at_mut(index);
        let (mid_slice, upper_slice) = upper_slice.split_at_mut(1);
        let node = &mut mid_slice[0];
        for to_id in mem::take(&mut node.to_nodes).into_keys() {
            let to_index = self.node_id_to_index[&to_id];
            let to_node = match to_index.cmp(&index) {
                cmp::Ordering::Less => &mut lower_slice[to_index],
                cmp::Ordering::Equal => {
                    unreachable!("Invalid state; node cannot self reference")
                }
                cmp::Ordering::Greater => &mut upper_slice[to_index - index - 1],
            };
            to_node.from_nodes.remove(&node.id);
        }

        for from_id in mem::take(&mut node.from_nodes).into_iter() {
            let from_index = self.node_id_to_index[&from_id];
            let from_node = match from_index.cmp(&index) {
                cmp::Ordering::Less => &mut lower_slice[from_index],
                cmp::Ordering::Equal => {
                    unreachable!("Invalid state; node cannot self reference")
                }
                cmp::Ordering::Greater => &mut upper_slice[from_index - index - 1],
            };
            from_node.to_nodes.remove(&node.id);
        }
    }

    pub fn detach_all_nodes(&mut self) {
        let ids: Vec<String> = self.node_id_to_index.keys().cloned().collect();
        for id in ids {
            self.detach_node(&id);
        }
    }

    pub fn clear(&mut self) {
        self.nodes = Vec::new();
        self.node_id_to_index = HashMap::new();
    }

    pub fn is_connected(
        &self,
        from_id: &str,
        to_id: &str,
        search_type: SearchType,
    ) -> Result<bool, InvalidNodeErr> {
        if !self.node_id_to_index.contains_key(from_id)
            || !self.node_id_to_index.contains_key(to_id)
            || from_id == to_id
        {
            return Err(InvalidNodeErr);
        }
        let mut probed = HashSet::<&str>::from([from_id]);
        let mut deque = VecDeque::<&str>::from(vec![from_id]);

        loop {
            let curr_id = match search_type {
                SearchType::DepthFirst => deque.pop_back(),
                SearchType::BreathFirst => deque.pop_front(),
            };

            match curr_id {
                Some(curr_id) if curr_id == to_id => return Ok(true),
                Some(curr_id) => {
                    let curr_node = self.get_node_unchecked(curr_id);
                    for curr_to_id in curr_node.to_nodes.keys() {
                        if !probed.contains(curr_to_id.as_str()) {
                            probed.insert(curr_to_id);
                            deque.push_back(curr_to_id);
                        }
                    }
                }
                None => return Ok(false),
            }
        }
    }

    // return vec of IDs and path from previous point, make sure to include self node
    pub fn get_shortest_path(
        &self,
        from_id: &str,
        to_id: &str,
    ) -> Result<Vec<(&String, usize)>, InvalidNodeErr> {
        if !self.node_id_to_index.contains_key(from_id)
            || !self.node_id_to_index.contains_key(to_id)
        {
            return Err(InvalidNodeErr);
        }
        let mut distances: HashMap<&String, usize> = self
            .node_id_to_index
            .keys()
            .map(|k| (k, usize::MAX))
            .collect();
        let mut visited: HashMap<&String, bool> =
            self.node_id_to_index.keys().map(|k| (k, false)).collect();
        let mut prev_ids: HashMap<&String, Option<&String>> =
            self.node_id_to_index.keys().map(|k| (k, None)).collect();

        // set starting to 0
        let from_id = self.get_node_id_ref_unchecked(from_id);
        let to_id = self.get_node_id_ref_unchecked(to_id);
        distances.insert(from_id, 0);
        let mut heap = BinaryHeap::from([cmp::Reverse((0usize, from_id))]);

        while let Some(item) = heap.pop() {
            let (distance, curr_id) = item.0;
            visited.insert(curr_id, true);
            if curr_id == to_id {
                break;
            }
            if distances[to_id] <= distance {
                continue;
            }

            let curr_distance = distances[curr_id];
            let to_ids = &self.get_node_unchecked(&curr_id).to_nodes;
            for (to_id, weight) in to_ids {
                if !visited[to_id] {
                    if distances[to_id] > curr_distance + weight {
                        distances.insert(to_id, curr_distance + weight);
                        prev_ids.insert(to_id, Some(curr_id));
                    }
                    heap.push(cmp::Reverse((distances[to_id], to_id)));
                };
            }
        }

        let paths = match visited[to_id] {
            false => Vec::<(&String, usize)>::new(),
            true => {
                // trace back to origin
                let mut curr_id = Some(to_id);
                let mut paths = Vec::<(&String, usize)>::new();
                while let Some(id) = curr_id {
                    let prev_id = prev_ids[id];
                    let weight = match prev_id {
                        Some(prev_id) => match self.get_edge_weight(prev_id, id) {
                            Some(weight) => weight,
                            None => unreachable!(
                                "Invalid state; if previous node exists, weight must exist"
                            ),
                        },
                        None => &0,
                    };
                    paths.push((id, *weight));
                    curr_id = prev_id;
                }
                paths.into_iter().rev().collect()
            }
        };

        Ok(paths)
    }

    fn get_node_id_ref_unchecked(&self, id: &str) -> &String {
        &self.get_node_unchecked(id).id
    }

    fn get_node_unchecked(&self, id: &str) -> &Node {
        &self.nodes[self.node_id_to_index[id]]
    }

    fn get_node_mut_unchecked(&mut self, id: &str) -> &mut Node {
        &mut self.nodes[self.node_id_to_index[id]]
    }

    pub fn iter_nodes(&self) -> IterNodes {
        IterNodes {
            node_iter: self.nodes.iter(),
        }
    }

    pub fn iter_to_edges(&self, id: &str) -> IterToEdges {
        IterToEdges {
            to_edges_iter: self.get_node_unchecked(id).to_nodes.iter(),
        }
    }

    pub fn iter_to_edges_mut(&mut self, id: &str) -> IterToEdgesMut {
        IterToEdgesMut {
            to_edges_iter_mut: self.get_node_mut_unchecked(id).to_nodes.iter_mut(),
        }
    }

    pub fn iter_from_edges(&self, id: &str) -> IterFromEdges {
        IterFromEdges {
            graph: self,
            from_edges_iter: self.get_node_unchecked(id).from_nodes.iter(),
            id: id.to_string(),
        }
    }

    pub fn iter_from_edges_mut(&mut self, id: &str) -> IterFromEdgesMut {
        let from_nodes: Vec<String> = self
            .get_node_unchecked(id)
            .from_nodes
            .iter()
            .cloned()
            .collect();
        IterFromEdgesMut {
            graph: self,
            from_nodes,
            id: id.to_string(),
        }
    }
}

impl Default for DirectedGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Eq, PartialEq, Debug)]
pub struct NodeItem<'a> {
    id: &'a String,
    to: &'a HashMap<String, usize>,
    from: &'a HashSet<String>,
}

#[derive(PartialEq)]
pub struct EdgeItem<'a> {
    id: &'a String,
    weight: &'a usize,
}

#[derive(PartialEq)]
pub struct EdgeItemMut<'a> {
    id: &'a String,
    weight: &'a mut usize,
}

pub struct IterNodes<'a> {
    node_iter: std::slice::Iter<'a, Node>,
}

impl<'a> Iterator for IterNodes<'a> {
    type Item = NodeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.node_iter.next().map(|item| NodeItem {
            id: &item.id,
            to: &item.to_nodes,
            from: &item.from_nodes,
        })
    }
}

pub struct IterToEdges<'a> {
    to_edges_iter: std::collections::hash_map::Iter<'a, String, usize>,
}

impl<'a> Iterator for IterToEdges<'a> {
    type Item = EdgeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_edges_iter.next().map(|item| EdgeItem {
            id: item.0,
            weight: item.1,
        })
    }
}

pub struct IterToEdgesMut<'a> {
    to_edges_iter_mut: std::collections::hash_map::IterMut<'a, String, usize>,
}

impl<'a> Iterator for IterToEdgesMut<'a> {
    type Item = EdgeItemMut<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_edges_iter_mut.next().map(|item| EdgeItemMut {
            id: item.0,
            weight: item.1,
        })
    }
}

pub struct IterFromEdges<'a> {
    graph: &'a DirectedGraph,
    from_edges_iter: std::collections::hash_set::Iter<'a, String>,
    id: String,
}

impl<'a> Iterator for IterFromEdges<'a> {
    type Item = EdgeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.from_edges_iter.next().map(|item| {
            let node = self.graph.get_node_unchecked(item.as_str());
            EdgeItem {
                id: &node.id,
                weight: &node.to_nodes[&self.id],
            }
        })
    }
}

pub struct IterFromEdgesMut<'a> {
    graph: &'a mut DirectedGraph,
    from_nodes: Vec<String>,
    id: String,
}

impl<'a> Iterator for IterFromEdgesMut<'a> {
    type Item = EdgeItemMut<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.from_nodes.pop() {
            Some(item) => {
                let node = self.graph.get_node_mut_unchecked(item.as_str());
                let weight = node.to_nodes.get_mut(&self.id).unwrap();
                let weight_ptr: *mut usize = weight;
                let node_id = &node.id;
                let node_id_ptr: *const String = node_id;
                Some(EdgeItemMut {
                    id: unsafe { node_id_ptr.as_ref().unwrap() },
                    weight: unsafe { weight_ptr.as_mut().unwrap() },
                })
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;
    use std::{
        fs::{self, read},
        path,
    };

    type GraphShape = HashMap<String, HashMap<String, usize>>;
    type IsConnectedData = HashMap<String, HashMap<String, bool>>;
    type ShortestPathData = HashMap<String, HashMap<String, Vec<(String, usize)>>>;

    fn read_json_data() -> Value {
        let json_string = fs::read_to_string(path::Path::new("./unit_test_data/graph.json"))
            .expect("Unable to read file");
        serde_json::from_str(json_string.as_str()).unwrap()
    }

    fn get_graph_shape() -> GraphShape {
        let json_data = read_json_data();
        let data = json_data["graph"].as_object().unwrap();
        let mut nodes: HashMap<String, HashMap<String, usize>> = HashMap::new();
        for node_id in data.keys() {
            nodes.insert(node_id.clone(), HashMap::new());
        }
        for (node_id, edges) in data {
            for (to_node_id, weight) in edges.as_object().unwrap() {
                let weight = usize::try_from(weight.as_u64().unwrap()).unwrap();
                nodes.entry(node_id.clone()).and_modify(|v| {
                    v.insert(to_node_id.clone(), weight);
                });
            }
        }
        nodes
    }

    fn get_node_ids() -> Vec<String> {
        get_graph_shape().into_keys().collect()
    }

    fn get_is_connected_data() -> IsConnectedData {
        let json_data = read_json_data();
        let data = json_data["is_connected"].as_object().unwrap();
        let mut node_connections: HashMap<String, HashMap<String, bool>> = HashMap::new();
        for node_id in data.keys() {
            node_connections.insert(node_id.clone(), HashMap::new());
        }
        for (from_node_id, to_nodes) in data {
            for (to_node_id, is_connected) in to_nodes.as_object().unwrap() {
                let is_connected = is_connected.as_bool().unwrap();
                node_connections
                    .entry(from_node_id.clone())
                    .and_modify(|v| {
                        v.insert(to_node_id.clone(), is_connected);
                    });
            }
        }
        node_connections
    }

    fn get_shortest_path_data() -> ShortestPathData {
        let json_data = read_json_data();
        let data = json_data["shortest_path"].as_object().unwrap();
        let mut shortest_paths: ShortestPathData = HashMap::new();
        for node_id in data.keys() {
            shortest_paths.insert(node_id.clone(), HashMap::new());
        }
        for (from_node_id, to_nodes) in data {
            for (to_node_id, path_nodes) in to_nodes.as_object().unwrap() {
                let path_item = path_nodes
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|item| {
                        let item = item.as_object().unwrap();
                        let node_id = item["node"].as_str().unwrap();
                        let weight = usize::try_from(item["weight"].as_u64().unwrap()).unwrap();
                        (node_id.to_string(), weight)
                    })
                    .collect();
                shortest_paths.entry(from_node_id.clone()).and_modify(|v| {
                    v.insert(to_node_id.clone(), path_item);
                });
            }
        }
        shortest_paths
    }

    fn gen_test_graph() -> DirectedGraph {
        let mut graph = DirectedGraph::new();
        let data = get_graph_shape();
        for node_id in data.keys() {
            let _ = graph.add_node(node_id.clone());
        }
        for (node_id, edges) in data {
            for (to_node_id, weight) in edges {
                let _ = graph.assign_edge(node_id.clone(), to_node_id, weight);
            }
        }
        graph
    }

    #[test]
    fn test_new() {
        // new()
        let graph = DirectedGraph::new();
        assert_eq!(
            graph,
            DirectedGraph {
                nodes: Vec::new(),
                node_id_to_index: HashMap::new()
            }
        );

        // default()
        let graph = DirectedGraph::default();
        assert_eq!(
            graph,
            DirectedGraph {
                nodes: Vec::new(),
                node_id_to_index: HashMap::new()
            }
        );
    }

    #[test]
    fn test_add_remove_nodes() {
        let node_ids: Vec<String> = get_node_ids();
        let mut graph = DirectedGraph::new();
        // insert and verify
        for (index, id) in node_ids.iter().enumerate() {
            assert_eq!(graph.get_node(id), None);
            assert_eq!(graph.add_node(id.clone()), Ok(()));
            assert_eq!(
                graph.get_node(id),
                Some(&Node {
                    id: id.clone(),
                    to_nodes: HashMap::new(),
                    from_nodes: HashSet::new()
                })
            );
            assert_eq!(graph.add_node(id.clone()), Err(DuplicateNodeErr));
            assert!(!graph.is_empty());
            assert_eq!(graph.size(), index + 1);
        }

        // remove and verify
        for (index, id) in node_ids.iter().enumerate() {
            assert!(!graph.is_empty());
            assert_eq!(graph.size(), node_ids.len() - index);
            assert_eq!(
                graph.get_node(id),
                Some(&Node {
                    id: id.clone(),
                    to_nodes: HashMap::new(),
                    from_nodes: HashSet::new()
                })
            );
            assert!(graph.remove_node(id));
            assert_eq!(graph.get_node(id), None);
            assert!(!graph.remove_node(id));
        }

        assert!(graph.is_empty());
        assert_eq!(graph.size(), 0);
    }

    #[test]
    fn test_assign_remove_edges() {
        let graph_shape = get_graph_shape();
        let mut graph = DirectedGraph::new();

        // add nodes and verify no edges
        for (node_id, edges) in graph_shape.iter() {
            let _ = graph.add_node(node_id.clone());
            for to_node_id in edges.keys() {
                assert_eq!(graph.get_edge_weight(node_id, to_node_id), None);
            }
        }

        // add_edges and verify
        for (node_id, edges) in graph_shape.iter() {
            for (to_node_id, weight) in edges {
                assert_eq!(
                    graph.assign_edge(node_id.clone(), to_node_id.clone(), *weight),
                    Ok(None)
                );
                assert_eq!(graph.get_edge_weight(node_id, to_node_id), Some(weight));
            }
        }

        // update edges and verify
        for (node_id, edges) in graph_shape.iter() {
            for (to_node_id, weight) in edges {
                assert_eq!(
                    graph.assign_edge(node_id.clone(), to_node_id.clone(), *weight + 10),
                    Ok(Some(*weight))
                );
                assert_eq!(
                    graph.get_edge_weight(node_id, to_node_id),
                    Some(&(*weight + 10))
                );
            }
        }

        // remove edges and verify
        for (node_id, edges) in graph_shape.iter() {
            for (to_node_id, weight) in edges {
                assert_eq!(graph.remove_edge(node_id, to_node_id), Some(*weight + 10));
                assert_eq!(graph.get_edge_weight(node_id, to_node_id), None);
            }
        }
    }

    #[test]
    fn test_assign_remove_edges_non_existent_node() {
        let mut graph = DirectedGraph::new();
        // verify edge empty node
        assert_eq!(graph.get_edge_weight("A", "B"), None);
        assert_eq!(graph.get_edge_weight("B", "A"), None);

        // assign_edge fails
        assert_eq!(
            graph.assign_edge("A".to_string(), "B".to_string(), 10),
            Err(InvalidNodeErr)
        );
        assert_eq!(
            graph.assign_edge("B".to_string(), "A".to_string(), 20),
            Err(InvalidNodeErr)
        );
        // remove edge empty node
        assert_eq!(graph.remove_edge("A", "B"), None);
        assert_eq!(graph.remove_edge("B", "A"), None);
    }

    #[test]
    fn test_assign_remove_edges_same_from_to_ids_fails() {
        let mut graph = DirectedGraph::new();
        // add only 1 node
        let _ = graph.add_node("A".to_string());
        // edge operations
        assert_eq!(
            graph.assign_edge("A".to_string(), "A".to_string(), 10),
            Err(InvalidNodeErr)
        );

        assert_eq!(graph.get_edge_weight("A", "A"), None);
        assert_eq!(graph.remove_edge("A", "A"), None);
    }

    #[test]
    fn test_add_remove_nodes_with_edges() {
        let graph_shape = get_graph_shape();

        for node_id in graph_shape.keys() {
            let mut graph = gen_test_graph();
            assert!(graph.get_node(node_id).is_some());
            assert!(graph.remove_node(node_id));
            assert_eq!(graph.get_node(node_id), None);
            for node in graph.iter_nodes() {
                assert_ne!(node.id, node_id);
                assert!(!node.to.contains_key(node_id));
                assert!(!node.from.contains(node_id));
            }
        }
    }

    #[test]
    fn test_detach_single_node() {
        let graph_shape = get_graph_shape();
        let node_ids = graph_shape.keys();

        for node_id in node_ids {
            let mut graph = gen_test_graph();
            assert!(graph.get_node(node_id).is_some());
            graph.detach_node(node_id);
            assert!(graph.get_node(node_id).is_some());

            for node in graph.iter_nodes() {
                if node.id != node_id {
                    assert!(!node.to.contains_key(node_id));
                    assert!(!node.from.contains(node_id));
                } else {
                    assert!(node.to.is_empty());
                    assert!(node.from.is_empty());
                }
            }
        }
    }

    #[test]
    fn test_detach_non_existent_node() {
        let mut graph = gen_test_graph();
        assert!(!graph.detach_node("non_existent"));
    }

    #[test]
    fn test_detach_all_nodes() {
        // empty
        let mut graph = DirectedGraph::new();
        graph.detach_all_nodes();
        assert!(graph.is_empty());

        // non-empty
        let mut graph = gen_test_graph();
        let graph_shape = get_graph_shape();
        graph.detach_all_nodes();
        for node_id in graph_shape.keys() {
            assert_eq!(
                graph.get_node(node_id),
                Some(&Node {
                    id: node_id.to_string(),
                    to_nodes: HashMap::new(),
                    from_nodes: HashSet::new()
                })
            );
        }
    }

    #[test]
    fn test_clear_graph() {
        // empty
        let mut graph = DirectedGraph::new();
        graph.clear();
        assert_eq!(
            graph,
            DirectedGraph {
                nodes: Vec::new(),
                node_id_to_index: HashMap::new()
            }
        );

        // non-empty
        let mut graph = gen_test_graph();
        graph.clear();
        assert_eq!(
            graph,
            DirectedGraph {
                nodes: Vec::new(),
                node_id_to_index: HashMap::new()
            }
        );
    }

    #[test]
    fn test_is_connected() {
        let graph = gen_test_graph();
        let node_ids: Vec<String> = get_node_ids();
        let data = get_is_connected_data();

        for from_node_id in node_ids.iter() {
            for to_node_id in node_ids.iter() {
                for search_type in [SearchType::DepthFirst, SearchType::BreathFirst] {
                    let result = graph.is_connected(from_node_id, to_node_id, search_type);
                    if from_node_id == to_node_id {
                        assert_eq!(result, Err(InvalidNodeErr))
                    } else {
                        assert_eq!(result, Ok(data[from_node_id][to_node_id]));
                    }
                }
            }
        }
    }

    #[test]
    fn test_is_connected_fails_non_existent_node() {
        let graph = gen_test_graph();
        let node_ids: Vec<String> = get_node_ids();

        for node_id in node_ids.iter() {
            assert_eq!(
                graph.is_connected(node_id, "NonExistent", SearchType::DepthFirst),
                Err(InvalidNodeErr)
            );
            assert_eq!(
                graph.is_connected(node_id, "NonExistent", SearchType::BreathFirst),
                Err(InvalidNodeErr)
            );
            assert_eq!(
                graph.is_connected("NonExistent", node_id, SearchType::DepthFirst),
                Err(InvalidNodeErr)
            );
            assert_eq!(
                graph.is_connected("NonExistent", node_id, SearchType::BreathFirst),
                Err(InvalidNodeErr)
            );
        }
    }

    #[test]
    fn test_shortest_paths() {
        let graph = gen_test_graph();
        let node_ids: Vec<String> = get_node_ids();
        let data = get_shortest_path_data();

        for from_node_id in node_ids.iter() {
            for to_node_id in node_ids.iter() {
                assert_eq!(
                    graph.get_shortest_path(from_node_id, to_node_id),
                    Ok(data[from_node_id][to_node_id]
                        .iter()
                        .map(|item| (&item.0, item.1))
                        .collect())
                );
            }
        }
    }

    #[test]
    fn test_shortest_paths_non_existent_node() {
        let graph = gen_test_graph();
        let node_ids: Vec<String> = get_node_ids();

        for node_id in node_ids.iter() {
            assert_eq!(
                graph.get_shortest_path(node_id, "NonExistent"),
                Err(InvalidNodeErr)
            );
            assert_eq!(
                graph.get_shortest_path("NonExistent", node_id),
                Err(InvalidNodeErr)
            );
        }
    }

    #[test]
    fn test_iter_nodes() {
        let graph = DirectedGraph::new();
        let mut iter = graph.iter_nodes();
        assert_eq!(iter.next(), None);

        let graph_shape = get_graph_shape();
        let graph = gen_test_graph();
        for node in graph.iter_nodes() {
            let node_id = node.id;
            let from_nodes: HashSet<String> = HashSet::from_iter(
                graph_shape
                    .iter()
                    .filter(|(_key, val)| val.contains_key(node_id))
                    .map(|(key, _val)| key.clone()),
            );
            assert_eq!(HashSet::from_iter(node.from.iter().cloned()), from_nodes);
            assert_eq!(node.to, &graph_shape[node_id]);
        }
    }

    #[test]
    fn test_iter_to_edges() {
        let graph = gen_test_graph();
        for node in graph.iter_nodes() {
            let to_edges: HashMap<String, usize> = graph
                .iter_to_edges(node.id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(&to_edges, node.to);
        }
    }

    #[test]
    fn test_iter_to_edges_mut() {
        let mut graph = gen_test_graph();
        for node_id in get_node_ids() {
            let mut expected_to_edges = graph.get_node(&node_id).unwrap().to_nodes.clone();
            let to_edges: HashMap<String, usize> = graph
                .iter_to_edges_mut(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(to_edges, expected_to_edges);

            // add 10 weight
            graph.iter_to_edges_mut(&node_id).for_each(|item| {
                *item.weight += 10;
            });

            // add 10 weight to expected edges
            expected_to_edges.values_mut().for_each(|item| {
                *item += 10;
            });
            // refetch to edges
            let to_edges: HashMap<String, usize> = graph
                .iter_to_edges(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(to_edges, expected_to_edges);
        }
    }

    #[test]
    fn test_iter_from_edges() {
        let graph = gen_test_graph();
        for node in graph.iter_nodes() {
            let expected_from_edges: HashMap<String, usize> = node
                .from
                .iter()
                .map(|item| (item.clone(), *graph.get_edge_weight(item, node.id).unwrap()))
                .collect();
            let from_edges: HashMap<String, usize> = graph
                .iter_from_edges(node.id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(from_edges, expected_from_edges);
        }
    }

    #[test]
    fn test_iter_from_edges_mut() {
        let mut graph = gen_test_graph();

        for node_id in get_node_ids() {
            let mut expected_from_edges = graph
                .get_node(&node_id)
                .unwrap()
                .from_nodes
                .iter()
                .map(|item| {
                    (
                        item.clone(),
                        *graph.get_edge_weight(item, &node_id).unwrap(),
                    )
                })
                .collect();
            let from_edges: HashMap<String, usize> = graph
                .iter_from_edges_mut(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(from_edges, expected_from_edges);

            // add 10 weight
            graph.iter_from_edges_mut(&node_id).for_each(|item| {
                *item.weight += 10;
            });

            // add 10 weight to expected edges
            expected_from_edges.values_mut().for_each(|item| {
                *item += 10;
            });
            // refetch from edges
            let from_edges: HashMap<String, usize> = graph
                .iter_from_edges(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();

            assert_eq!(from_edges, expected_from_edges);
        }
    }
}
