import dataclasses as _dataclasses
from pprint import PrettyPrinter
from proof_generation.proof import MetaVar, Mu, Implication, bot


class SuccintPrinter(PrettyPrinter):
    @staticmethod
    def _is_empty(obj) -> bool:
        return obj in {(), None}

    def _pprint_dataclass(self, object, stream, indent, allowance, context, level) -> None:
        """
        Use shorthands for field names if the object's class offer them.
        Field names (but not values) are omitted if corr. shorthand is the empty-string.
        Fields are omitted entirely if the value is "empty-like".
        """
        cls_name = object.__class__
        shorthand = {}
        if hasattr(cls_name, 'shorthand'):
            shorthand = cls_name.shorthand()
        cls_output_name: str = shorthand.get('__name__', object.__class__.__name__)

        indent += len(cls_output_name) + 1
        # https://docs.python.org/3.7/library/dataclasses.html#dataclasses.dataclass
        # Fields order is guaranteed to be definition order
        items = [(shorthand.get(f.name, f.name), getattr(object, f.name)) for f in _dataclasses.fields(object)]
        items = list(filter((lambda item: not SuccintPrinter._is_empty(item[1])), items))

        # Pretty-print bottom
        if object == bot:
            stream.write('\u22A5')
            return 

        # Pretty-print negation
        if isinstance(object, Implication) and object.right == bot:
            stream.write('\u00AC')

            #Recompute indent
            indent -= len(cls_output_name) + 1
            indent += 1

            # Don't print bot anymore
            items.remove(('', object.right))

            self._format_namespace_items(items, stream, indent, allowance, context, level)
            return

        # Special formatting for MetaVars
        if isinstance(object, MetaVar):
            phi_name = f'phi{object.name}'

            #Recompute indent
            indent -= len(cls_output_name) + 1
            indent += len(phi_name)

            stream.write(phi_name)

            #Avoid duplication when formatting field values further down
            cls_output_name = ""
            items.remove(('', object.name))
        
        if len(items) > 0:
            stream.write(cls_output_name + '(')
            self._format_namespace_items(items, stream, indent, allowance, context, level)
            stream.write(')')

    def _format_namespace_items(self, items, stream, indent, allowance, context, level) -> None:
        write = stream.write
        delimnl = ',\n' + ' ' * indent
        last_index = len(items) - 1
        for i, (key, ent) in enumerate(items):
            last = i == last_index
            if len(key) > 0:
                write(key)
                write('=')

            if id(ent) in context:
                # Special-case representation of recursion to match standard
                # recursive dataclass repr.
                write('...')
            else:
                self._format(ent, stream, indent + len(key) + 1, allowance if last else 1, context, level)
            if not last:
                write(delimnl)
