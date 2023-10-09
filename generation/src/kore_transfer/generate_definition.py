import argparse

from pyk.ktool.kompile import kompile


def main(k_file: str, output_dir: str) -> None:
    print(f'Kompiling target {k_file} to {output_dir}')
    kompile(main_file=k_file, backend='llvm', output_dir=output_dir)
    return


if __name__ == '__main__':
    argparser = argparse.ArgumentParser()
    # First argument: path to the .K file
    argparser.add_argument('k_file', type=str)
    # Second argument: path to the program
    argparser.add_argument('program', type=str)
    # Path to the output directory
    argparser.add_argument('output_dir', type=str)
    args = argparser.parse_args()

    main(args.k_file, args.output_dir)
