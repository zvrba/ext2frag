/*
  ext2frag.cc, (c) 2008 Zeljko Vrba <zvrba@ifi.uio.no>

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to
  deal in the Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
  sell copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
  IN THE SOFTWARE.

  ============================================================================

  Download and build e2fsprogs-1.41.  Compile this source with the following
  command line:

  g++ -g -W -Wall -O2 ext2frag.cc -I ~/COMPILE/e2fsprogs-1.41.0/lib	\
  ~/COMPILE/e2fsprogs-1.41.0/lib/ext2fs/libext2fs.a					\
  ~/COMPILE/e2fsprogs-1.41.0/lib/libcom_err.a -o extf2rag

  (Obviously, you should specify the correct build directory of e2fsprogs.)

  ============================================================================
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>
#include <deque>
#include <algorithm>
#include <numeric>
#include <utility>
#include <vector>
#include <boost/ref.hpp>
#include <boost/lambda/lambda.hpp>
#include <boost/lambda/bind.hpp>
#include <ext2fs/ext2_fs.h>
#include <ext2fs/ext2fs.h>

using std::cout;
using std::cerr;
using std::endl;

typedef std::pair<unsigned, unsigned> pair2u;

struct block_range : public pair2u
{
	block_range() : pair2u(0, 0) { }
	block_range(unsigned a, unsigned b) : pair2u(a, b) { }

	unsigned size() const
	{
		assert(first <= second);
		return second - first + 1;
	}
};

typedef std::vector<block_range> range_list;

struct file_fragments
{
	unsigned	inode;
	unsigned 	size;
	unsigned	inversions;
	int			last_logical;
	range_list	blocks;

	file_fragments(unsigned i_, unsigned s_) :
		inode(i_), size(s_), inversions(0), last_logical(-1)
	{
		assert(blocks.empty());
	}
};

typedef std::deque<file_fragments> file_fragment_list;

static void collect_free_blocks(ext2_filsys, range_list&);
static void collect_file_blocks(ext2_filsys, file_fragment_list&);
static void print_range_list(std::ostream&, const range_list&);
static void print_file_list(const file_fragment_list&);
static void print_summary(
	const range_list&, const file_fragment_list&, unsigned, unsigned);

#define E2CHECK(fn, ...) do {					\
		errcode_t err__ = fn(__VA_ARGS__);		\
		if(!err__) break;						\
		com_err(#fn, err__, 0);					\
		exit(1);								\
	} while(0)

//////////////////////////////////////////////////////////////////////////////

static void usage(const char *argv0)
{
	cerr << "USAGE: " << argv0 << " -[v] EXT2IMAGE\n";
	cerr << "\t-v add verbose output\n";
	exit(1);
}

int main(int argc, char **argv)
{
	range_list free_blocks;
	file_fragment_list file_blocks;
	ext2_filsys fs;
	unsigned blocksize, blockcnt;
	int opt = 0, verbose = 0;

	initialize_ext2_error_table();
	while(opt != -1) {
		switch(opt = getopt(argc, argv, "vh")) {
		case 'v':
			verbose = 1;
			break;
		case -1:
			break;
		default:
			usage(argv[0]);
		}
	}

	// There must be exactly one non-option argument.

	if(optind != argc-1)
		usage(argv[0]);
	
	E2CHECK(ext2fs_open, argv[optind], 0, 0, 0, unix_io_manager, &fs);
	
	blocksize = 1U << (10 + fs->super->s_log_block_size);
	blockcnt = fs->super->s_blocks_count;
	
	E2CHECK(ext2fs_read_bitmaps, fs);
	collect_free_blocks(fs, free_blocks);
	collect_file_blocks(fs, file_blocks);
	E2CHECK(ext2fs_close, fs);

	if(verbose) {
		cout << "F:";
		print_range_list(cout, free_blocks);
		cout << endl;
		print_file_list(file_blocks);
	}

	print_summary(free_blocks, file_blocks, blocksize, blockcnt);
		
	return 0;
}

//////////////////////////////////////////////////////////////////////////////

static void extend_range(range_list &blocks, unsigned b)
{
	if(blocks.empty()) {
		blocks.push_back(block_range(b, b));
	} else {
		block_range &last = blocks.back();

		if(last.second+1 == b)
			last.second = b;
		else
			blocks.push_back(block_range(b, b));
	}
}

static void collect_free_blocks(ext2_filsys fs, range_list &blocks)
{
	if(!fs->block_map) {
		cerr << "Block map not present\n";
		return;
	}

	for(unsigned i = fs->super->s_first_data_block; i < fs->super->s_blocks_count; i++)
		if(!ext2fs_test_block_bitmap(fs->block_map, i))
			extend_range(blocks, i);
}

//////////////////////////////////////////////////////////////////////////////

static int data_block_cb(ext2_filsys, blk_t *bnr, int cnt, void *closure)
{
	// The assertion checks that logical blocks are reported in strictly
	// increasing order.  The blocks logical are not sequential if the file
	// has holes.
	
	file_fragments &ff = *static_cast<file_fragments*>(closure);
	assert(cnt > ff.last_logical); // Ensure that logical blocks are reported
	ff.last_logical = cnt;		   // in strictly increasing order.
	extend_range(ff.blocks, *bnr);
	return 0;
}

//
// Count the number of backward jumps in the block list of the file.
//
static unsigned count_inversions(const range_list &rl)
{
	using namespace boost::lambda;
	range_list::const_iterator it = rl.begin();
	unsigned n = 0;
	
	while(1) {
		it = std::adjacent_find(it, rl.end(), bind(&pair2u::first, _1) > bind(&pair2u::first, _2));
		if(it == rl.end())
			break;
		++it; ++n;
	}
	return n;
}

static void collect_file_blocks(ext2_filsys fs, file_fragment_list &fl)
{
	ext2_inode_scan scan;
	ext2_ino_t ino;
	ext2_inode inode;
	char buf[65536];

	E2CHECK(ext2fs_open_inode_scan, fs, 1024, &scan);
	E2CHECK(ext2fs_inode_scan_flags, scan, EXT2_SF_SKIP_MISSING_ITABLE, 0);
	while(1) {
		E2CHECK(ext2fs_get_next_inode, scan, &ino, &inode);
		if(!ino)
			break;
		if(!ext2fs_test_inode_bitmap(fs->inode_map, ino))
			continue;
		if(!LINUX_S_ISREG(inode.i_mode) || !inode.i_size || (ino < EXT2_GOOD_OLD_FIRST_INO))
			continue;

		file_fragments ff(ino, inode.i_size);
		E2CHECK(ext2fs_block_iterate, fs, ino, BLOCK_FLAG_DATA_ONLY,
				buf, data_block_cb, &ff);
		ff.inversions = count_inversions(ff.blocks);
		fl.push_back(ff);
	}
	ext2fs_close_inode_scan(scan);
}

//////////////////////////////////////////////////////////////////////////////

static inline unsigned count_blocks(const range_list &rl)
{
	using namespace boost::lambda;
	
	return std::accumulate(
		rl.begin(), rl.end(), 0U, _1 + bind(&block_range::size, _2));
}

template<typename T>
static inline typename T::const_reference quartile(const T &v, int p)
{
	unsigned idx = (v.size()-1) * p / 4;
	return v[idx];
}

static inline void expand_range(std::vector<unsigned> &v, const block_range &b)
{
	for(unsigned i = b.first; i <= b.second; ++i)
		v.push_back(i);
}

static void expand_range_list(std::vector<unsigned> &v, const range_list &rl)
{
	using namespace boost::lambda;
	std::for_each(rl.begin(), rl.end(), bind(expand_range, boost::ref(v), _1));
}

//
// Output a 5-number summary of the  dataset (min, 1st quartile, median, 2nd
// quartile, max).
//
static void summary5(const char *title, const std::vector<unsigned> &v)
{
	cout << title;
	if(!v.size()) {
		cout << "na";
	} else {
		for(int i = 0; i < 5; i++)
			cout << quartile(v, i) << ',';
	}
	cout << endl;
}

//
// Must extend lambda's type deduction system to handle ULL types
//
namespace boost {
namespace lambda {

template<class Act>
struct plain_return_type_2<arithmetic_action<Act>, unsigned long long, unsigned int>
{
	typedef unsigned long long type;
};

}
}

static void print_summary(
	const range_list &free_blocks,
	const file_fragment_list &files,
	unsigned blocksize,
	unsigned blockcount)
{
	using namespace boost::lambda;

	unsigned total_free_blocks;
	unsigned total_file_blocks, total_file_fragments;
	unsigned total_inverted_files, total_inversions;
	unsigned long long total_file_bytes;
	std::vector<unsigned> tmp;
	
	total_free_blocks = count_blocks(free_blocks);
	cout << "H:block_size=" << blocksize << endl
		 << "H:total_blocks=" << blockcount << endl
		 << "H:free_blocks=" << total_free_blocks << endl
		 << "H:free_extents=" << free_blocks.size() << endl;

	tmp.clear();
	std::transform(free_blocks.begin(), free_blocks.end(),
				   std::back_insert_iterator<std::vector<unsigned> >(tmp),
				   bind(&block_range::size, _1));
	std::sort(tmp.begin(), tmp.end());

	summary5("H:free_extent_size_summary=", tmp);
	cout << "H:ext_frag=" << 1 - tmp.back() / (double)total_free_blocks << endl;

	total_file_blocks = std::accumulate(
		files.begin(), files.end(), 0,
		_1 + bind(count_blocks, bind(&file_fragments::blocks, _2)));
	total_file_bytes = std::accumulate(
		files.begin(), files.end(), 0ULL,
		_1 + bind(&file_fragments::size, _2));
	total_file_fragments = std::accumulate(
		files.begin(), files.end(), 0U,
		_1 + bind(&range_list::size, bind(&file_fragments::blocks, _2)));

	cout << "H:total_files=" << files.size() << endl
		 << "H:file_blocks=" << total_file_blocks << endl
		 << "H:file_bytes=" << total_file_bytes << endl
		 << "H:file_fragments=" << total_file_fragments << endl;

	tmp.clear();
	std::transform(
		files.begin(), files.end(),
		std::back_insert_iterator<std::vector<unsigned> >(tmp),
		bind(&file_fragments::size, _1));
	std::sort(tmp.begin(), tmp.end());

	summary5("H:file_size_summary=", tmp);
	
	cout << "H:data_frag=" << (double)total_file_fragments / files.size() << endl
		 << "H:int_frag="
		 << (double)total_file_blocks * blocksize / total_file_bytes << endl;

	total_inverted_files = std::count_if(
		files.begin(), files.end(), bind(&file_fragments::inversions, _1) > 0);
	total_inversions = std::accumulate(
		files.begin(), files.end(), 0U, _1 + bind(&file_fragments::inversions, _2));
										 
	cout << "H:backward_files=" << total_inverted_files << endl
		 << "H:backward_jumps=" << total_inversions << endl;

	tmp.clear();
	std::for_each(
		files.begin(), files.end(),
		bind(expand_range_list, boost::ref(tmp), bind(&file_fragments::blocks, _1)));
	std::sort(tmp.begin(), tmp.end());
	summary5("H:file_locations_summary=", tmp);
}

//////////////////////////////////////////////////////////////////////////////

static std::ostream &operator<<(std::ostream &os, const block_range &r)
{
	if(r.first == r.second)
		os << r.first;
	else
		os << r.first << '-' << r.second;
	return os;
}

static void print_range_list(std::ostream &os, const range_list &rl)
{
	// XXX! bug report?!  gcc4.2.1 reports an error unless block_range is
	// default constructible..
	std::copy(rl.begin(), rl.end(), std::ostream_iterator<block_range>(os, ","));
}

static std::ostream &operator<<(std::ostream &os, const file_fragments &ff)
{
	os << "R:" << ff.inode << ';' << ff.size << ";";
	print_range_list(os, ff.blocks);
	return os;
}

static void print_file_list(const file_fragment_list &ff)
{
	std::copy(ff.begin(), ff.end(), std::ostream_iterator<file_fragments>(cout, "\n"));
}
