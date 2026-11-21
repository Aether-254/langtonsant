import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1855 : checkSingleBlackFast (-58, -39) 20816 .north (31, 27) (-57, -19) = true := by
  decide +kernel

end LangtonsAnt
