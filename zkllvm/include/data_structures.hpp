#include <cassert>
#include <cstdlib>
#include <iostream>

void *memset_(void *ptr, int value, size_t num) {
  auto *byte_ptr = (unsigned char *)ptr;
  auto byte_value = (unsigned char)value;

  for (size_t i = 0; i < num; i++) {
    byte_ptr[i] = byte_value;
  }

  return ptr;
}

template <typename T> struct Node {
  T data;
  Node *next;

  explicit Node(const T &value) noexcept : data(value), next(nullptr) {}

  bool operator==(const Node &rhs) const noexcept { return equal(*this, rhs); }

  bool operator!=(const Node &rhs) noexcept { return !(this->operator==(rhs)); }

  static Node *create(const T &value) noexcept {
    Node *newNode = static_cast<Node *>(std::malloc(sizeof(Node)));
    memset_(newNode, 0, sizeof(Node));
    newNode->data = value;
    newNode->next = nullptr;
    return newNode;
  }
};

template <typename T>
bool equal(const Node<T> &lhs, const Node<T> &rhs) noexcept {

  return lhs.data.operator==(rhs.data) && lhs.next == rhs.next;
}

template <> bool equal(const Node<int> &lhs, const Node<int> &rhs) noexcept {

  if (!lhs.data && !rhs.data) {
    return true;
  } else if (!lhs.data || !rhs.data) {
    return false;
  }
  return lhs.data == rhs.data && (*lhs.next == *rhs.next);
}

template <typename T> class LinkedList {
public:
  Node<T> *head = nullptr;

  LinkedList() noexcept : head(nullptr) {}

  ~LinkedList() noexcept {
    Node<T> *curr = head;
    while (curr) {
      Node<T> *next = curr->next;
      curr->~Node();
      free(curr);
      curr = next;
    }
  }

  bool operator==(const LinkedList &rhs) const noexcept {
    if (!head && !rhs.head) {
      return true;
    } else if (!head || !rhs.head) {
      return false;
    }
    return (*head == *rhs.head);
  }

  bool operator!=(const LinkedList &rhs) noexcept { return !(*this == rhs); }

  void push(const T &value) noexcept {
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

  void push_back(const T &value) noexcept {
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

  T pop() noexcept {
    assert(head && "Insufficient stack items.");
    T value = head->data;

    // Update the head
    Node<T> *next = head->next;
    std::free(head);
    head = next;

    return value;
  }

  void clear() noexcept {
    while (head) {
      Node<T> *next = head->next;
      head->~Node();
      std::free(head);
      head = next;
    }
  }

  T front() noexcept {
    assert(head && "Insufficient stack items.");
    return head->data;
  }

  static LinkedList *create() noexcept {
    auto newList = static_cast<LinkedList *>(std::malloc(sizeof(LinkedList)));
    newList->head = nullptr;
    return newList;
  }

  static LinkedList *create(const T &value) noexcept {
    LinkedList *list = create();
    list->push(value);
    return list;
  }

  bool contains(const T &value) noexcept {
    Node<T> *curr = head;
    while (curr) {
      if (curr->data == value) {
        return true;
      }
      curr = curr->next;
    }
    return false;
  }

  bool containsElementOf(LinkedList<T> *otherList) noexcept {
    for (auto &item : *this) {
      if (otherList->contains(item)) {
        return true;
      }
    }
    return false;
  }

  T &get(int index) noexcept {
    Node<T> *curr = head;
    for (int i = 0; i < index; i++) {
      curr = curr->next;
      assert(curr && "Index out of bounds.");
    }
    return curr->data;
  }

  T &operator[](int index) noexcept { return get(index); }

  size_t size() noexcept {
    size_t count = 0;
    Node<T> *curr = head;
    while (curr) {
      count++;
      curr = curr->next;
    }
    return count;
  }

  bool empty() noexcept { return head == nullptr; }

  class Iterator {
  private:
    Node<T> *current;

  public:
    Iterator(Node<T> *head) noexcept : current(head) {}

    T &operator*() noexcept { return current->data; }
    T *operator->() noexcept { return &current->data; }
    bool operator==(const Iterator &other) noexcept {
      return current == other.current;
    }
    bool operator!=(const Iterator &other) noexcept {
      return current != other.current;
    }

    Iterator &operator++() noexcept {
      current = current->next;
      return *this;
    }
  };

  Iterator begin() noexcept { return Iterator(head); }
  Iterator end() noexcept { return Iterator(nullptr); }

#ifdef DEBUG
  void print() noexcept {
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
