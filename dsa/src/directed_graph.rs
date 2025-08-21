//! Directed-graph implementation using index pointers technique

use std::{
    cmp,
    collections::{BinaryHeap, HashMap, HashSet, VecDeque},
    mem,
};

/// Directed graph structure
///
/// * `nodes`: node vector
/// * `node_indices`: hashmap of node IDs to indices in node vector
#[derive(Debug, PartialEq)]
pub struct DirectedGraph {
    nodes: Vec<Node>,
    node_indices: HashMap<String, usize>, // id, index
}

#[derive(Debug, PartialEq)]
/// Directed graph node structure
///
/// * `id`: node ID
/// * `out_bound_edges`: out-bound edges
/// * `in_bound_edges`: in-bound edges
pub struct Node {
    pub id: String,
    pub out_bound_edges: HashMap<String, usize>, // dest node ID to weight
    pub in_bound_edges: HashSet<String>,
}

#[derive(Debug)]
pub enum SearchType {
    DepthFirst,
    BreadthFirst,
}

#[derive(Debug, PartialEq)]
pub struct DuplicateNodeErr;

#[derive(Debug, PartialEq)]
pub struct InvalidNodeErr;

impl DirectedGraph {
    /// Create new directed graph
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert_eq!(graph.size(), 0);
    /// assert!(graph.is_empty());
    ///
    /// ```
    pub fn new() -> DirectedGraph {
        DirectedGraph {
            nodes: Vec::new(),
            node_indices: HashMap::new(),
        }
    }

    /// Get whether directed graph is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// assert!(!graph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Get number of nodes stored in directed graph
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// assert!(!graph.is_empty());
    /// ```
    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    /// Add a node
    ///
    /// * `id`: node ID string
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// assert!(!graph.is_empty());
    /// ```
    pub fn add_node(&mut self, id: String) -> Result<(), DuplicateNodeErr> {
        if !self.node_indices.contains_key(&id) {
            // push node to node vec
            self.nodes.push(Node {
                id: id.clone(),
                out_bound_edges: HashMap::new(),
                in_bound_edges: HashSet::new(),
            });

            // bookkeep new node index
            self.node_indices.insert(id, self.nodes.len() - 1);
            Ok(())
        } else {
            // node with ID already exists
            Err(DuplicateNodeErr)
        }
    }

    /// Assign directional edge between 2 nodes
    ///
    /// * `src_node_id`: source node ID
    /// * `dest_node_id`: destination node ID
    /// * `weight`: edge weight
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// assert_eq!(graph.get_edge_weight("A", "B"), Some(&3));
    /// ```
    pub fn assign_edge(
        &mut self,
        src_node_id: String,
        dest_node_id: String,
        weight: usize,
    ) -> Result<Option<usize>, InvalidNodeErr> {
        if let Some(src_node_index) = self.node_indices.get(&src_node_id)
            && let Some(dest_node_index) = self.node_indices.get(&dest_node_id)
            && src_node_id != dest_node_id
        {
            // attempt getting mutable reference to source and destination node
            let (src_node, dest_node) = self.get_two_nodes_mut(*src_node_index, *dest_node_index);

            // connect nodes by assigning edge to source node's out-bound edges and destination
            // node's in-bound edges
            let old_weight = src_node.out_bound_edges.insert(dest_node_id, weight);
            dest_node.in_bound_edges.insert(src_node_id);
            // return old weight if it exists
            Ok(old_weight)
        } else {
            // Either source node or destination node does not exist, or if node IDs are equal
            Err(InvalidNodeErr)
        }
    }

    /// Get node
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::{DirectedGraph, Node};
    /// use std::collections::{HashMap, HashSet};
    ///
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node("A".to_string());
    /// assert_eq!(graph.get_node("A"), Some(&Node {
    ///     id: "A".to_string(),
    ///     out_bound_edges: HashMap::new(),
    ///     in_bound_edges: HashSet::new()
    ///
    /// }));
    /// assert_eq!(graph.get_node("B"), None);
    /// ```
    pub fn get_node(&self, id: &str) -> Option<&Node> {
        if let Some(index) = self.node_indices.get(id) {
            Some(&self.nodes[*index])
        } else {
            // node does not exist
            None
        }
    }

    /// Get edge weight between nodes
    ///
    /// * `src_node_id`: source node ID
    /// * `dest_node_id`: destination node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// assert_eq!(graph.get_edge_weight("A", "B"), Some(&3));
    /// assert_eq!(graph.get_edge_weight("A", "C"), None);
    pub fn get_edge_weight(&self, src_node_id: &str, dest_node_id: &str) -> Option<&usize> {
        if let Some(src_node_index) = self.node_indices.get(src_node_id) {
            let src_node = &self.nodes[*src_node_index];
            // if destination node does not exist, or not connected from source node, None is
            // returned
            src_node.out_bound_edges.get(dest_node_id)
        } else {
            // source node does not exist
            None
        }
    }

    /// Remove node
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::{DirectedGraph, Node};
    /// use std::collections::{HashMap, HashSet};
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// assert_eq!(graph.get_node("A"), Some(&Node {
    ///     id: "A".to_string(),
    ///     out_bound_edges: HashMap::new(),
    ///     in_bound_edges: HashSet::new()
    ///
    /// }));
    /// assert!(graph.remove_node("A"));
    /// assert_eq!(graph.get_node("A"), None);
    /// assert!(!graph.remove_node("B"));
    /// ```
    pub fn remove_node(&mut self, id: &str) -> bool {
        match self.node_indices.get_mut(id) {
            // node exists
            Some(index) => {
                let index = *index;
                // detach all connected edges in-bound or out-bound
                self.detach_node_unchecked(index);
                // using swap_remove to remove node; record ID of last node in node vec for
                // bookkeeping
                let last_id = self.nodes.last().unwrap().id.clone();
                self.nodes.swap_remove(index);
                // update node indices map due to last node being swapped in place of removed node,
                // then remove reference to removed node in node indices map
                // note: if the node to remove happen to be last node in vec, it'll still be
                // removed from node indices map in the end.
                self.node_indices.insert(last_id, index);
                self.node_indices.remove(id);
                true
            }
            // node does not exist
            None => false,
        }
    }

    /// Remove edge
    ///
    /// * `from_id`: from-node ID
    /// * `to_id`: to-node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// assert_eq!(graph.get_edge_weight("A", "B"), Some(&3));
    /// graph.remove_edge("A", "B");
    /// assert_eq!(graph.get_edge_weight("A", "B"), None);
    /// ```
    pub fn remove_edge(&mut self, src_node_id: &str, dest_node_id: &str) -> Option<usize> {
        if let Some(src_node_index) = self.node_indices.get(src_node_id)
            && let Some(to_index) = self.node_indices.get(dest_node_id)
            && src_node_index != to_index
        {
            // get mutable reference of source and destination node
            let (src_node, dest_node) = self.get_two_nodes_mut(*src_node_index, *to_index);
            // remove from source node's out-bound edges map
            let weight = src_node.out_bound_edges.remove(dest_node_id);
            // if edge entry exists, remove from destination node's in-bound edges set
            if weight.is_some() {
                dest_node.in_bound_edges.remove(src_node_id);
            }
            // return weight of removed edge
            weight
        } else {
            // Either source node or destination node does not exist, or if node IDs are equal
            None
        }
    }

    /// Utility function to get mutable reference to source and destination node
    ///
    /// * `src_node_index`: index of source node in node vec
    /// * `dest_node_index`: index of destination node in node vec
    ///
    /// Warning: function will panic if:
    /// - indices do not exist in vec
    /// - indices are equal.
    fn get_two_nodes_mut(
        &mut self,
        src_node_index: usize,
        dest_node_index: usize,
    ) -> (&mut Node, &mut Node) {
        // use source node index as split point to split node vec
        let (lower_slice, upper_slice) = self.nodes.split_at_mut(src_node_index);

        let (src_node, dest_node) = match src_node_index.cmp(&dest_node_index) {
            // source node index is less than destination node index
            // destination node is in upper slice
            cmp::Ordering::Less => {
                // source node and destination node both exist in upper slice,
                // must split again to avoid borrow-checker violation
                let (src_node_slice, upper_slice) = upper_slice.split_at_mut(1);
                (
                    &mut src_node_slice[0],
                    &mut upper_slice[dest_node_index - src_node_index - 1],
                )
            }
            // caller should ensure 2 indices are not equal
            cmp::Ordering::Equal => {
                unreachable!("source node index cannot be equal to destination node index")
            }
            // source node index is greater than destination node index
            // destination node is in lower slice
            cmp::Ordering::Greater => (&mut upper_slice[0], &mut lower_slice[dest_node_index]),
        };

        // return mutable references
        (src_node, dest_node)
    }

    /// Detach node
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// graph.assign_edge("A".to_string(), "C".to_string(), 4);
    /// assert_eq!(graph.get_edge_weight("A", "B"), Some(&3));
    /// assert_eq!(graph.get_edge_weight("A", "C"), Some(&4));
    /// graph.detach_node("A");
    /// assert_eq!(graph.get_edge_weight("A", "B"), None);
    /// assert_eq!(graph.get_edge_weight("A", "C"), None);
    /// ```
    pub fn detach_node(&mut self, id: &str) -> bool {
        match self.node_indices.get(id) {
            // node exists
            Some(index) => {
                self.detach_node_unchecked(*index);
                true
            }
            // node does not exist
            None => false,
        }
    }

    /// Detach node unchecked
    ///
    /// * `index`: index of node to detach in node vec
    ///
    /// Warning: function will panic if:
    /// - indices to not exist in vec
    fn detach_node_unchecked(&mut self, index: usize) {
        // get node, clone ID for use later, take node's in/out-bound edges
        let node = &mut self.nodes[index];
        let node_id = node.id.clone();
        let out_bound_edges = mem::take(&mut node.out_bound_edges);
        let in_bound_edges = mem::take(&mut node.in_bound_edges);

        // for each node in to_nodes, remove in-bound edge from target node
        for dest_node_id in out_bound_edges.into_keys() {
            let dest_node_index = self.node_indices[&dest_node_id];
            let dest_node = &mut self.nodes[dest_node_index];
            dest_node.in_bound_edges.remove(&node_id);
        }

        // for each node in in-bound edges, remove out-bound edge to target node
        for src_node_id in in_bound_edges.into_iter() {
            let src_node_index = self.node_indices[&src_node_id];
            let src_node = &mut self.nodes[src_node_index];
            src_node.out_bound_edges.remove(&node_id);
        }
    }

    /// Detach all nodes
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// graph.assign_edge("B".to_string(), "C".to_string(), 4);
    /// graph.assign_edge("C".to_string(), "A".to_string(), 5);
    /// assert_eq!(graph.get_edge_weight("A", "B"), Some(&3));
    /// assert_eq!(graph.get_edge_weight("B", "C"), Some(&4));
    /// assert_eq!(graph.get_edge_weight("C", "A"), Some(&5));
    /// graph.detach_all_nodes();
    /// assert_eq!(graph.get_edge_weight("A", "B"), None);
    /// assert_eq!(graph.get_edge_weight("B", "C"), None);
    /// assert_eq!(graph.get_edge_weight("C", "A"), None);
    /// ```
    pub fn detach_all_nodes(&mut self) {
        let ids: Vec<String> = self.node_indices.keys().cloned().collect();
        // call detach_node on all node IDs
        for id in ids {
            self.detach_node(&id);
        }
    }

    /// Clear graph
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// graph.assign_edge("B".to_string(), "C".to_string(), 4);
    /// graph.assign_edge("C".to_string(), "A".to_string(), 5);
    /// assert_eq!(graph.get_edge_weight("A", "B"), Some(&3));
    /// assert_eq!(graph.get_edge_weight("B", "C"), Some(&4));
    /// assert_eq!(graph.get_edge_weight("C", "A"), Some(&5));
    /// graph.clear();
    /// assert_eq!(graph, DirectedGraph::new());
    /// ```
    pub fn clear(&mut self) {
        self.nodes = Vec::new();
        self.node_indices = HashMap::new();
    }

    /// Check if there is connection from a source node to destination node
    ///
    /// * `src_node_id`: source node ID
    /// * `dest_node_id`: destination node ID
    /// * `search_type`: search type (breadth-first/depth-first)
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::{DirectedGraph, SearchType};
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// graph.assign_edge("B".to_string(), "C".to_string(), 4);
    /// assert_eq!(graph.is_connected("A", "B", SearchType::DepthFirst), Ok(true));
    /// assert_eq!(graph.is_connected("B", "C", SearchType::BreadthFirst), Ok(true));
    /// assert_eq!(graph.is_connected("A", "C", SearchType::DepthFirst), Ok(true));
    /// assert_eq!(graph.is_connected("B", "A", SearchType::BreadthFirst), Ok(false));
    /// assert_eq!(graph.is_connected("C", "B", SearchType::DepthFirst), Ok(false));
    /// assert_eq!(graph.is_connected("C", "A", SearchType::BreadthFirst), Ok(false));
    /// ```
    pub fn is_connected(
        &self,
        src_node_id: &str,
        dest_node_id: &str,
        search_type: SearchType,
    ) -> Result<bool, InvalidNodeErr> {
        if !self.node_indices.contains_key(src_node_id)
            || !self.node_indices.contains_key(dest_node_id)
            || src_node_id == dest_node_id
        {
            return Err(InvalidNodeErr);
        }
        let mut probed = HashSet::<&str>::from([src_node_id]);
        let mut deque = VecDeque::<&str>::from(vec![src_node_id]);

        loop {
            let curr_node_id = match search_type {
                SearchType::DepthFirst => deque.pop_back(),
                SearchType::BreadthFirst => deque.pop_front(),
            };

            match curr_node_id {
                Some(curr_node_id) if curr_node_id == dest_node_id => return Ok(true),
                Some(curr_node_id) => {
                    let curr_node = self.get_node_unchecked(curr_node_id);
                    for src_node_id in curr_node.out_bound_edges.keys() {
                        if !probed.contains(src_node_id.as_str()) {
                            probed.insert(src_node_id);
                            deque.push_back(src_node_id);
                        }
                    }
                }
                None => return Ok(false),
            }
        }
    }

    /// Get shortest path, and return nodes and edge weights along path
    ///
    /// * `src_node_id`: source node ID
    /// * `dest_node_id`: destination node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.add_node("D".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// graph.assign_edge("B".to_string(), "D".to_string(), 4);
    /// graph.assign_edge("A".to_string(), "C".to_string(), 4);
    /// graph.assign_edge("C".to_string(), "D".to_string(), 4);
    /// assert_eq!(graph.get_shortest_path("A", "D"), Ok(vec![
    ///     (&"A".to_string(), 0),
    ///     (&"B".to_string(), 3),
    ///     (&"D".to_string(), 4),
    /// ]));
    /// ```
    pub fn get_shortest_path(
        &self,
        src_node_id: &str,
        dest_node_id: &str,
    ) -> Result<Vec<(&String, usize)>, InvalidNodeErr> {
        if !self.node_indices.contains_key(src_node_id)
            || !self.node_indices.contains_key(dest_node_id)
        {
            // if source/destination node is not present, return error
            return Err(InvalidNodeErr);
        }

        // path tracking maps; distances, whether a node is visited, and previous node IDs
        let mut distances: HashMap<&String, usize> =
            self.node_indices.keys().map(|k| (k, usize::MAX)).collect();
        let mut visited: HashMap<&String, bool> =
            self.node_indices.keys().map(|k| (k, false)).collect();
        let mut prev_node_ids: HashMap<&String, Option<&String>> =
            self.node_indices.keys().map(|k| (k, None)).collect();

        // get reference to source/destination ID within source
        let src_node_id = self.get_node_id_ref_unchecked(src_node_id);
        let dest_node_id = self.get_node_id_ref_unchecked(dest_node_id);

        // set source node distance to 0
        distances.insert(src_node_id, 0);

        // create min-heap (using cmp::Reverse), insert source node into heap
        let mut heap = BinaryHeap::from([cmp::Reverse((0usize, src_node_id))]);

        // continue popping from heap until heap is exhausted, or destination node
        // is found
        while let Some(item) = heap.pop() {
            // unpack heap item
            let (distance, curr_node_id) = item.0;
            // mark current node as visited
            visited.insert(curr_node_id, true);

            // if destination node reached, break
            if curr_node_id == dest_node_id {
                break;
            }

            // if heap item's distance is larger than recorded distance, skip processing.
            // Rust's heap does not support updating priority, so we'll just ignore ones
            // with lower priority
            if distances[dest_node_id] <= distance {
                continue;
            }

            // the distance exists because distances are updated when heap item is pushed
            let curr_distance = distances[curr_node_id];
            // get all out-bound edges
            let out_bound_edges = &self.get_node_unchecked(curr_node_id).out_bound_edges;

            // for each out-bound node in out-bound edges, if the node has not been visited,
            // and if out-bound node distance calculated from current node's distance is shorter,
            // update new shorter distance, and update previous node ID for out-bound node
            // update its distance from current node's distance if its shorter.
            for (out_bound_node_id, weight) in out_bound_edges {
                if !visited[out_bound_node_id] {
                    if distances[out_bound_node_id] > curr_distance + weight {
                        distances.insert(out_bound_node_id, curr_distance + weight);
                        prev_node_ids.insert(out_bound_node_id, Some(curr_node_id));
                    }
                    // if node is not visited, it's not been processed, push it onto heap
                    heap.push(cmp::Reverse((
                        distances[out_bound_node_id],
                        out_bound_node_id,
                    )));
                };
            }
        }

        let paths = match visited[dest_node_id] {
            // if destination node is not visited, there is no path so return empty vec
            false => Vec::<(&String, usize)>::new(),
            // destination node is visited, backtrack path nodes
            true => {
                let mut paths = Vec::<(&String, usize)>::new();
                let mut curr_node_id = Some(dest_node_id);

                // from current node ID, get previous node ID and the edge weight between two,
                // until current node does not have previous node
                while let Some(id) = curr_node_id {
                    let prev_node_id = prev_node_ids[id];
                    let weight = match prev_node_id {
                        Some(prev_node_id) => match self.get_edge_weight(prev_node_id, id) {
                            Some(weight) => weight,
                            None => unreachable!(
                                "Invalid state; if previous node exists, weight must exist"
                            ),
                        },
                        None => &0,
                    };
                    // record current node ID and edge weight
                    paths.push((id, *weight));
                    // set current node ID to previous node ID
                    curr_node_id = prev_node_id;
                }
                // destination node is recorded first, so reverse path
                paths.into_iter().rev().collect()
            }
        };

        Ok(paths)
    }

    /// Get reference to node ID string
    ///
    /// * `id`: node ID string slice
    fn get_node_id_ref_unchecked(&self, id: &str) -> &String {
        &self.get_node_unchecked(id).id
    }

    /// Get reference to node
    ///
    /// * `id`: node ID string slice
    fn get_node_unchecked(&self, id: &str) -> &Node {
        &self.nodes[self.node_indices[id]]
    }

    /// Get mutable reference to node
    ///
    /// * `id`: node ID string slice
    fn get_node_mut_unchecked(&mut self, id: &str) -> &mut Node {
        &mut self.nodes[self.node_indices[id]]
    }

    /// Iterator for nodes
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::{DirectedGraph, NodeItem};
    /// use std::collections::HashSet;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// let nodes: HashSet<String> = HashSet::from_iter(graph
    ///     .iter_nodes()
    ///     .map(|item| item.id.clone())
    /// );
    /// let expected_nodes = HashSet::from_iter(vec![
    ///     "A".to_string(),
    ///     "B".to_string(),
    ///     "C".to_string()
    /// ].into_iter());
    /// assert_eq!(nodes, expected_nodes);
    /// ```
    pub fn iter_nodes(&self) -> IterNodes {
        IterNodes {
            node_iter: self.nodes.iter(),
        }
    }

    /// Immutable iterator for a node's out-bound edges
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// use std::collections::HashMap;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// graph.assign_edge("A".to_string(), "C".to_string(), 4);
    /// let nodes: HashMap<String, usize> = HashMap::from_iter(graph
    ///     .iter_out_bound_edges("A")
    ///     .map(|item| (item.id.clone(), *item.weight)));
    /// let expected_nodes: HashMap<String, usize> = HashMap::from_iter(vec![
    ///     ("B".to_string(), 3),
    ///     ("C".to_string(), 4)
    /// ]);
    /// assert_eq!(nodes, expected_nodes);
    /// ```
    pub fn iter_out_bound_edges(&self, id: &str) -> IterOutBoundEdges {
        IterOutBoundEdges {
            out_bound_edges_iter: self.get_node_unchecked(id).out_bound_edges.iter(),
        }
    }

    /// Mutable iterator for a node's out-bound edges
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::{DirectedGraph, EdgeItemMut};
    /// use std::collections::HashMap;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.assign_edge("A".to_string(), "B".to_string(), 3);
    /// let edge_item = graph.iter_out_bound_edges_mut("A").next().unwrap();
    /// assert_eq!(edge_item, EdgeItemMut { id: &"B".to_string(), weight: &mut 3usize});
    /// *edge_item.weight += 2;
    /// let edge_item = graph.iter_out_bound_edges_mut("A").next().unwrap();
    /// assert_eq!(edge_item, EdgeItemMut { id: &"B".to_string(), weight: &mut 5usize});
    /// ```
    pub fn iter_out_bound_edges_mut(&mut self, id: &str) -> IterOutBoundEdgesMut {
        IterOutBoundEdgesMut {
            out_bound_edges_iter_mut: self.get_node_mut_unchecked(id).out_bound_edges.iter_mut(),
        }
    }

    /// Immutable iterator for a node's in-bound edges
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::DirectedGraph;
    /// use std::collections::HashMap;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.add_node("C".to_string());
    /// graph.assign_edge("B".to_string(), "A".to_string(), 3);
    /// graph.assign_edge("C".to_string(), "A".to_string(), 4);
    /// let nodes: HashMap<String, usize> = HashMap::from_iter(graph
    ///     .iter_in_bound_edges("A")
    ///     .map(|item| (item.id.clone(), *item.weight)));
    /// let expected_nodes: HashMap<String, usize> = HashMap::from_iter(vec![
    ///     ("B".to_string(), 3),
    ///     ("C".to_string(), 4)
    /// ]);
    /// assert_eq!(nodes, expected_nodes);
    /// ```
    pub fn iter_in_bound_edges(&self, id: &str) -> IterInBoundEdges {
        IterInBoundEdges {
            graph: self,
            in_bound_edges_iter: self.get_node_unchecked(id).in_bound_edges.iter(),
            id: id.to_string(),
        }
    }

    /// Mutable iterator for a node's in-bound edges
    ///
    /// * `id`: node ID
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::directed_graph::{DirectedGraph, EdgeItemMut};
    /// use std::collections::HashMap;
    /// let mut graph = DirectedGraph::new();
    /// assert!(graph.is_empty());
    /// graph.add_node("A".to_string());
    /// graph.add_node("B".to_string());
    /// graph.assign_edge("B".to_string(), "A".to_string(), 3);
    /// let edge_item = graph.iter_in_bound_edges_mut("A").next().unwrap();
    /// assert_eq!(edge_item, EdgeItemMut { id: &"B".to_string(), weight: &mut 3usize});
    /// *edge_item.weight += 2;
    /// let edge_item = graph.iter_in_bound_edges_mut("A").next().unwrap();
    /// assert_eq!(edge_item, EdgeItemMut { id: &"B".to_string(), weight: &mut 5usize});
    /// ```
    pub fn iter_in_bound_edges_mut(&mut self, id: &str) -> IterInBoundEdgesMut {
        let from_nodes: Vec<String> = self
            .get_node_unchecked(id)
            .in_bound_edges
            .iter()
            .cloned()
            .collect();
        IterInBoundEdgesMut {
            graph: self,
            src_node_ids: from_nodes,
            id: id.to_string(),
        }
    }
}

impl Default for DirectedGraph {
    /// Default implementation of directed graph
    fn default() -> Self {
        Self::new()
    }
}

/// Node item for node iterator
///
/// * `id`: node ID
/// * `out_bound_edges`: reference to out-bound edges
/// * `in_bound_edges`: reference to in-bound edges
#[derive(Eq, PartialEq, Debug)]
pub struct NodeItem<'a> {
    pub id: &'a String,
    pub out_bound_edges: &'a HashMap<String, usize>,
    pub in_bound_edges: &'a HashSet<String>,
}

/// Edge item for immutable edge iterator
///
/// * `id`: reference to node ID
/// * `weight`: reference to edge weight
#[derive(Debug, PartialEq)]
pub struct EdgeItem<'a> {
    pub id: &'a String,
    pub weight: &'a usize,
}

/// Edge item for mutable edge iterator
///
/// * `id`: reference to node ID
/// * `weight`: mutable reference to edge weight
#[derive(Debug, PartialEq)]
pub struct EdgeItemMut<'a> {
    pub id: &'a String,
    pub weight: &'a mut usize,
}

/// Node iterator struct
///
/// * `node_iter`: node vec slice
pub struct IterNodes<'a> {
    node_iter: std::slice::Iter<'a, Node>,
}

impl<'a> Iterator for IterNodes<'a> {
    type Item = NodeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.node_iter.next().map(|item| NodeItem {
            id: &item.id,
            out_bound_edges: &item.out_bound_edges,
            in_bound_edges: &item.in_bound_edges,
        })
    }
}

/// Out-bound edges iterator struct
///
/// * `node_iter`: iterator of out-bound edges
pub struct IterOutBoundEdges<'a> {
    out_bound_edges_iter: std::collections::hash_map::Iter<'a, String, usize>,
}

impl<'a> Iterator for IterOutBoundEdges<'a> {
    type Item = EdgeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.out_bound_edges_iter.next().map(|item| EdgeItem {
            id: item.0,
            weight: item.1,
        })
    }
}

/// Out-bound edges mutable iterator struct
///
/// * `to_edges_iter_mut`: mutable iterator of out-bound edges
pub struct IterOutBoundEdgesMut<'a> {
    out_bound_edges_iter_mut: std::collections::hash_map::IterMut<'a, String, usize>,
}

impl<'a> Iterator for IterOutBoundEdgesMut<'a> {
    type Item = EdgeItemMut<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.out_bound_edges_iter_mut
            .next()
            .map(|item| EdgeItemMut {
                id: item.0,
                weight: item.1,
            })
    }
}

/// In-bound edges iterator struct
///
/// * `graph`: immutable reference to graph
/// * `out_bound_edges_iter`: iterator of in-bound edges
/// * `id`: node ID
pub struct IterInBoundEdges<'a> {
    graph: &'a DirectedGraph,
    in_bound_edges_iter: std::collections::hash_set::Iter<'a, String>,
    id: String,
}

impl<'a> Iterator for IterInBoundEdges<'a> {
    type Item = EdgeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.in_bound_edges_iter.next().map(|item| {
            let node = self.graph.get_node_unchecked(item.as_str());
            EdgeItem {
                id: &node.id,
                weight: &node.out_bound_edges[&self.id],
            }
        })
    }
}

/// In-bound edges mutable iterator struct
///
/// * `graph`: mutable reference to graph
/// * `src_node_ids`: in-bound source node IDs
/// * `id`: node ID
pub struct IterInBoundEdgesMut<'a> {
    graph: &'a mut DirectedGraph,
    src_node_ids: Vec<String>,
    id: String,
}

impl<'a> Iterator for IterInBoundEdgesMut<'a> {
    type Item = EdgeItemMut<'a>;

    /// The use of unsafe in this function is sound.
    /// The returned struct from `next` has same lifetime as iterator struct itself, and each
    /// returned items from this function are distinct despite living in same data structure,
    /// so borrow checking rule won't be violated.
    fn next(&mut self) -> Option<Self::Item> {
        match self.src_node_ids.pop() {
            Some(item) => {
                // get in-bound source node and its weight
                let node = self.graph.get_node_mut_unchecked(item.as_str());
                let weight = node.out_bound_edges.get_mut(&self.id).unwrap();
                let node_id = &node.id;
                // convert weight reference to mutable pointer
                let weight_ptr: *mut usize = weight;
                // convert node ID reference to immutable pointer
                let node_id_ptr: *const String = node_id;
                // Re-convert pointers back to references, and return
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
    use std::{fs, path};

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
                node_indices: HashMap::new()
            }
        );

        // default()
        let graph = DirectedGraph::default();
        assert_eq!(
            graph,
            DirectedGraph {
                nodes: Vec::new(),
                node_indices: HashMap::new()
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
                    out_bound_edges: HashMap::new(),
                    in_bound_edges: HashSet::new()
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
                    out_bound_edges: HashMap::new(),
                    in_bound_edges: HashSet::new()
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
                assert!(!node.out_bound_edges.contains_key(node_id));
                assert!(!node.in_bound_edges.contains(node_id));
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
                    assert!(!node.out_bound_edges.contains_key(node_id));
                    assert!(!node.in_bound_edges.contains(node_id));
                } else {
                    assert!(node.out_bound_edges.is_empty());
                    assert!(node.in_bound_edges.is_empty());
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
                    out_bound_edges: HashMap::new(),
                    in_bound_edges: HashSet::new()
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
                node_indices: HashMap::new()
            }
        );

        // non-empty
        let mut graph = gen_test_graph();
        graph.clear();
        assert_eq!(
            graph,
            DirectedGraph {
                nodes: Vec::new(),
                node_indices: HashMap::new()
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
                for search_type in [SearchType::DepthFirst, SearchType::BreadthFirst] {
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
                graph.is_connected(node_id, "NonExistent", SearchType::BreadthFirst),
                Err(InvalidNodeErr)
            );
            assert_eq!(
                graph.is_connected("NonExistent", node_id, SearchType::DepthFirst),
                Err(InvalidNodeErr)
            );
            assert_eq!(
                graph.is_connected("NonExistent", node_id, SearchType::BreadthFirst),
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
            assert_eq!(
                HashSet::from_iter(node.in_bound_edges.iter().cloned()),
                from_nodes
            );
            assert_eq!(node.out_bound_edges, &graph_shape[node_id]);
        }
    }

    #[test]
    fn test_iter_to_edges() {
        let graph = gen_test_graph();
        for node in graph.iter_nodes() {
            let to_edges: HashMap<String, usize> = graph
                .iter_out_bound_edges(node.id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(&to_edges, node.out_bound_edges);
        }
    }

    #[test]
    fn test_iter_to_edges_mut() {
        let mut graph = gen_test_graph();
        for node_id in get_node_ids() {
            let mut expected_to_edges = graph.get_node(&node_id).unwrap().out_bound_edges.clone();
            let to_edges: HashMap<String, usize> = graph
                .iter_out_bound_edges_mut(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(to_edges, expected_to_edges);

            // add 10 weight
            graph.iter_out_bound_edges_mut(&node_id).for_each(|item| {
                *item.weight += 10;
            });

            // add 10 weight to expected edges
            expected_to_edges.values_mut().for_each(|item| {
                *item += 10;
            });
            // refetch to edges
            let to_edges: HashMap<String, usize> = graph
                .iter_out_bound_edges(&node_id)
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
                .in_bound_edges
                .iter()
                .map(|item| (item.clone(), *graph.get_edge_weight(item, node.id).unwrap()))
                .collect();
            let from_edges: HashMap<String, usize> = graph
                .iter_in_bound_edges(node.id)
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
                .in_bound_edges
                .iter()
                .map(|item| {
                    (
                        item.clone(),
                        *graph.get_edge_weight(item, &node_id).unwrap(),
                    )
                })
                .collect();
            let from_edges: HashMap<String, usize> = graph
                .iter_in_bound_edges_mut(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();
            assert_eq!(from_edges, expected_from_edges);

            // add 10 weight
            graph.iter_in_bound_edges_mut(&node_id).for_each(|item| {
                *item.weight += 10;
            });

            // add 10 weight to expected edges
            expected_from_edges.values_mut().for_each(|item| {
                *item += 10;
            });
            // refetch from edges
            let from_edges: HashMap<String, usize> = graph
                .iter_in_bound_edges(&node_id)
                .map(|item| (item.id.clone(), *item.weight))
                .collect();

            assert_eq!(from_edges, expected_from_edges);
        }
    }
}
