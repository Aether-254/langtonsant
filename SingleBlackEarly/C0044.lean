import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0044 : checkSingleBlackFast (-4, 1) 5547 .west (1, 2) (-17, -13) = true := by
  decide +kernel

end LangtonsAnt
