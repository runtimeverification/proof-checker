#include "../include/data_structures.hpp"

[[circuit]] int main() {
    LinkedList *myList = LinkedList::create();

    // Test insert, delete, and assert
    myList->insert_front(5);
    assert(myList->head->data == 5); // If it fails: UNREACHABLE at ${HOME}/zkllvm/libs/assigner/include/nil/blueprint/parser.hpp:721 Function _wassert has no implementation.

    myList->insert_front(10);
    assert(myList->head->data == 10);

    myList->delete_front();
    assert(myList->head->data == 5);

    return 0;
}