enum Node<T> {
    Data(T, Box<Node<T>>),
    Nil,
}
pub struct SinglyLinkedList<T> {
    head: Box<Node<T>>,
    size: usize,
}

impl<T> SinglyLinkedList<T> {
    pub fn new() -> SinglyLinkedList<T> {
        SinglyLinkedList {
            head: Box::new(Node::Nil),
            size: 0,
        }
    }

    // pub fn from_array(arr: &[T]) -> SinglyLinkedList<T> {}

    // pub fn get_ref(&self, index: usize) -> Option<&T>{ }

    // pub fn get_mut_ref(&mut self, index: usize) -> Option<&mut T>{ }

    pub fn len(&self) -> usize {
        return self.size;
    }

    pub fn is_empty(&self) -> bool {
        true
    }

    pub fn append(&self, item: T) {
        let new_node = Node::Data(item, Box::new(Node::Nil));
    }

    // pub fn prepend(&self, item: T) {}
}

impl<T> Default for SinglyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_test() {
        assert_eq!(2, 2);
    }
}
