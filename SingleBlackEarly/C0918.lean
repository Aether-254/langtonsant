import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0918 : checkSingleBlackFast (-7, 13) 28435 .west (3, -7) (-38, -13) = true := by
  decide +kernel

end LangtonsAnt
