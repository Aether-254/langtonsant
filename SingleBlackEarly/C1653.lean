import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1653 : checkSingleBlackFast (-43, -19) 13535 .west (8, 19) (-38, 0) = true := by
  decide +kernel

end LangtonsAnt
