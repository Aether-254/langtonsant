import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0105 : checkSingleBlackFast (-5, 4) 31281 .west (11, 15) (-43, -2) = true := by
  decide +kernel

end LangtonsAnt
