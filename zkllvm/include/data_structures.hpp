#include <cassert>
#include <cstdlib>
#include <iostream>

template <typename T> struct Node {
  T data;
  Node *next;

  Node(const T &value) : data(value), next(nullptr) {}

  bool operator==(const Node &rhs) const { return equal(*this, rhs); }

  bool operator!=(const Node &rhs) { return !(this == rhs); }

  static Node *create(const T &value) {
    Node *newNode = static_cast<Node *>(std::malloc(sizeof(Node)));
    newNode->data = value;
    newNode->next = nullptr;
    return newNode;
  }
};

template <typename T> bool equal(const Node<T> &lhs, const Node<T> &rhs) {

  if (!lhs.data && !rhs.data) {
    return true;
  } else if (!lhs.data || !rhs.data) {
    return false;
  }
  return lhs.data->operator==(*rhs.data) && lhs.next == rhs.next;
}

template <> bool equal(const Node<uint8_t> &lhs, const Node<uint8_t> &rhs) {

  if (!lhs.data && !rhs.data) {
    return true;
  } else if (!lhs.data || !rhs.data) {
    return false;
  }
  return lhs.data == rhs.data && lhs.next == rhs.next;
}

template <typename T> class LinkedList {
public:
  Node<T> *head = nullptr;

  LinkedList() : head(nullptr) {}

  ~LinkedList() {
    Node<T> *curr = head;
    while (curr) {
      Node<T> *next = curr->next;
      std::free(curr);
      curr = next;
    }
  }

  bool operator==(const LinkedList &rhs) const {
    if (!head && !rhs.head) {
      return true;
    } else if (!head || !rhs.head) {
      return false;
    }
    return (*head == *rhs.head);
  }

  bool operator!=(const LinkedList &rhs) { return !(*this == rhs); }

  void push(const T &value) {
    Node<T> *newNode = Node<T>::create(value);

    // If the list is empty, set the new node as the head
    if (head == nullptr) {
      head = newNode;
    } else {
      // Otherwise, update the links
      newNode->next = head;
      head = newNode;
    }
  }

  void push_back(const T &value) {
    Node<T> *newNode = Node<T>::create(value);

    // If the list is empty, set the new node as the head
    if (head == nullptr) {
      head = newNode;
    } else {
      // Otherwise, find the last node and update the links
      Node<T> *curr = head;
      while (curr->next) {
        curr = curr->next;
      }
      curr->next = newNode;
    }
  }

  T pop() {
    assert(head && "Insufficient stack items.");
    T value = head->data;

    // Update the head
    Node<T> *next = head->next;
    std::free(head);
    head = next;

    return value;
  }

  T front() {
    assert(head && "Insufficient stack items.");
    return head->data;
  }

  static LinkedList *create() {
    auto newList = static_cast<LinkedList *>(std::malloc(sizeof(LinkedList)));
    newList->head = nullptr;
    return newList;
  }

  static LinkedList *create(const T &value) {
    LinkedList *list = create();
    list->push(value);
    return list;
  }

  bool contains(const T &value) {
    Node<T> *curr = head;
    while (curr) {
      if (curr->data == value) {
        return true;
      }
      curr = curr->next;
    }
    return false;
  }

  bool isDisjoint(LinkedList<T> *otherList) {
    for (auto &item : *this) {
      if (otherList->contains(item)) {
        return false;
      }
    }
    return true;
  }

  T &get(int index) {
    Node<T> *curr = head;
    for (int i = 0; i < index; i++) {
      curr = curr->next;
      assert(curr && "Index out of bounds.");
    }
    return curr->data;
  }

  T &operator[](int index) { return get(index); }

  size_t size() {
    size_t count = 0;
    Node<T> *curr = head;
    while (curr) {
      count++;
      curr = curr->next;
    }
    return count;
  }

  bool empty() { return head == nullptr; }

  class Iterator {
  private:
    Node<T> *current;

  public:
    Iterator(Node<T> *head) : current(head) {}

    T &operator*() { return current->data; }
    T *operator->() { return &current->data; }
    bool operator==(const Iterator &other) { return current == other.current; }
    bool operator!=(const Iterator &other) { return current != other.current; }

    Iterator &operator++() {
      current = current->next;
      return *this;
    }

    Iterator next() {
      Iterator tmp = *this;
      ++(*this);
      return tmp;
    }
  };

  Iterator begin() { return Iterator(head); }
  Iterator end() { return Iterator(nullptr); }

#ifdef DEBUG
  void print() {
    if (!head) {
      std::cout << "[]";
      return;
    }
    Node<T> *curr = head;
    while (curr) {
      std::cout << (int)curr->data << " ";
      curr = curr->next;
    }
  }
#endif
};
