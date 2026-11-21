import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1057 : checkSingleBlackFast (-12, -1) 31708 .north (-2, -8) (2, -38) = true := by
  decide +kernel

end LangtonsAnt
