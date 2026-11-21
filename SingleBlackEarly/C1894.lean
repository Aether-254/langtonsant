import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1894 : checkSingleBlackFast (-65, -42) 19853 .east (30, 15) (7, -49) = true := by
  decide +kernel

end LangtonsAnt
