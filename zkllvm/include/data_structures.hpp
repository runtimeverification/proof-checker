#include <cassert>
#include <cstdlib>
#include <iostream>

template <typename T> struct Node {
  T data;
  Node *next;

  static Node *create(const T &value) {
    Node *newNode = static_cast<Node *>(std::malloc(sizeof(Node)));
    newNode->data = value;
    newNode->next = nullptr;
    return newNode;
  }
};

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

  void insert_front(const T &value) {
    Node<T> *newNode = Node<T>::create(value);

    // If the list is empty, set the new node as the head
    if (head == nullptr) {
      newNode->next = nullptr;
      head = newNode;
    } else {
      // Otherwise, update the links
      newNode->next = head;
      head = newNode;
    }
  }

  void delete_front() {
    if (!head) {
      return;
    }

    Node<T> *next = head->next;
    std::free(head);
    head = next;
  }

  static LinkedList *create() {
    auto newList = static_cast<LinkedList *>(std::malloc(sizeof(LinkedList)));
    newList->head = nullptr;
    return newList;
  }

  static LinkedList *create(const T &value) {
    LinkedList *list = create();
    list->insert_front(value);
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