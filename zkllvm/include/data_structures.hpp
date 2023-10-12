#include <cstdlib>
#include <cassert>

struct Node {
    int data;
    Node *next;

    static Node *create(const int &value) {
        Node *newNode = static_cast<Node *>(std::malloc(sizeof(Node *)));
        newNode->data = value;
        newNode->next = nullptr;
        return newNode;
    }
};


class LinkedList {
public:
    Node *head = nullptr;

    LinkedList() : head(nullptr) {}

    ~LinkedList() {
        Node *curr = head;
        while (curr) {
            Node *next = curr->next;
            std::free(curr);
            curr = next;
        }
    }

    static LinkedList *create() {
        return static_cast<LinkedList *>(std::malloc(sizeof(LinkedList *)));
    }

    void insert_front(const int &value) {
        Node *newNode = Node::create(value);
        newNode->data = value;

        // If the list is empty, set the new node as the head
        if (!head) {
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

        Node *next = head->next;
        std::free(head);
        head = next;
    }
};
