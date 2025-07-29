//! Directed-graph implementation using index pointers technique

use std::{
    cmp,
    collections::{BinaryHeap, HashMap, HashSet, VecDeque},
};

use serde_json::map::IterMut;

#[derive(Debug)]
struct DirectedGraph {
    nodes: Vec<Node>,
    node_id_to_index: HashMap<String, usize>, // id, index
}

#[derive(Debug)]
struct Node {
    id: String,
    to_nodes: HashMap<String, usize>, // to_id, weight
    from_nodes: HashSet<String>,
}

#[derive(Debug)]
enum SearchType {
    DepthFirst,
    BreathFirst,
}

#[derive(Debug)]
struct DuplicateNodeErr;
struct InvalidNodeErr;

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
                id,
                to_nodes: HashMap::new(),
                from_nodes: HashSet::new(),
            });
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

    pub fn remove_node(&mut self, id: &str) -> bool {
        match self.node_id_to_index.remove(id) {
            Some(index) => {
                let _ = self.detach_node(id);
                self.nodes.swap_remove(index);
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
                // split 3 part, lower slice, node at index, and upperslice
                let (lower_slice, upper_slice) = self.nodes.split_at_mut(*index);
                let (mid_slice, upper_slice) = upper_slice.split_at_mut(*index + 1);
                let node = &mid_slice[0];
                for (to_id, _) in &node.to_nodes {
                    let to_index = self.node_id_to_index[to_id];
                    let to_node = match to_index.cmp(&index) {
                        cmp::Ordering::Less => &mut lower_slice[to_index],
                        cmp::Ordering::Equal => {
                            unreachable!("Invalid state; node cannot self reference")
                        }
                        cmp::Ordering::Greater => &mut upper_slice[to_index - index - 1],
                    };
                    to_node.from_nodes.remove(to_id);
                }

                for from_id in &node.from_nodes {
                    let from_index = self.node_id_to_index[from_id];
                    let from_node = match from_index.cmp(&index) {
                        cmp::Ordering::Less => &mut lower_slice[from_index],
                        cmp::Ordering::Equal => {
                            unreachable!("Invalid state; node cannot self reference")
                        }
                        cmp::Ordering::Greater => &mut upper_slice[from_index - index - 1],
                    };
                    from_node.from_nodes.remove(from_id);
                }
                true
            }
            None => false,
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

    pub fn get_edge_weight(&self, from_id: &str, to_id: &str) -> Option<&usize> {
        if let Some(from_index) = self.node_id_to_index.get(from_id) {
            let from_node = &self.nodes[*from_index];
            from_node.to_nodes.get(to_id)
        } else {
            None
        }
    }

    pub fn is_connected(
        &self,
        from_id: &str,
        to_id: &str,
        search_type: SearchType,
    ) -> Result<bool, InvalidNodeErr> {
        if !self.node_id_to_index.contains_key(from_id)
            || !self.node_id_to_index.contains_key(to_id)
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
                    let curr_node = self.get_node(curr_id);
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
        let from_id = self.get_node_id(from_id);
        let to_id = self.get_node_id(to_id);
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
            let to_ids = &self.get_node(&curr_id).to_nodes;
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
            false => return Ok(vec![]),
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
                paths
            }
        };

        Ok(paths)
    }

    fn get_node_id(&self, id: &str) -> &String {
        &self.get_node(id).id
    }

    fn get_node(&self, id: &str) -> &Node {
        &self.nodes[self.node_id_to_index[id]]
    }

    fn get_node_mut(&mut self, id: &str) -> &mut Node {
        &mut self.nodes[self.node_id_to_index[id]]
    }

    pub fn iter_nodes(&self) -> IterNodes {
        IterNodes {
            node_iter: self.nodes.iter(),
        }
    }

    pub fn iter_to_edges(&self, id: &str) -> IterToEdges {
        IterToEdges {
            to_edges_iter: self.get_node(id).to_nodes.iter(),
        }
    }

    pub fn iter_mut_to_edges(&mut self, id: &str) -> IterMutToEdges {
        IterMutToEdges {
            to_edges_iter_mut: self.get_node_mut(id).to_nodes.iter_mut(),
        }
    }

    pub fn iter_from_edges(&self, id: &str) -> IterFromEdges {
        IterFromEdges {
            graph: self,
            from_edges_iter: self.get_node(id).from_nodes.iter(),
            id: id.to_string(),
        }
    }

    pub fn iter_mut_from_edges(&mut self, id: &str) -> IterMutFromEdges {
        let from_nodes: Vec<&String> = self.get_node(id).from_nodes.iter().collect();
        IterMutFromEdges {
            graph: self,
            from_nodes: from_nodes.iter(),
            id: id.to_string(),
        }
    }
}

pub struct NodeItem<'a> {
    id: &'a String,
    to: &'a HashMap<String, usize>,
    from: &'a HashSet<String>,
}

pub struct EdgeItem<'a> {
    id: &'a String,
    weight: &'a usize,
}

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

pub struct IterMutToEdges<'a> {
    to_edges_iter_mut: std::collections::hash_map::IterMut<'a, String, usize>,
}

impl<'a> Iterator for IterMutToEdges<'a> {
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
            let node = self.graph.get_node(item.as_str());
            EdgeItem {
                id: &node.id,
                weight: &node.to_nodes[&self.id],
            }
        })
    }
}

pub struct IterMutFromEdges<'a> {
    graph: &'a mut DirectedGraph,
    from_nodes: std::slice::Iter<'a, &'a String>,
    id: String,
}

impl<'a> Iterator for IterMutFromEdges<'a> {
    type Item = EdgeItemMut<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.from_nodes.next() {
            Some(item) => {
                let node = self.graph.get_node_mut(item.as_str());
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
    use std::{fs, path, vec};
}
