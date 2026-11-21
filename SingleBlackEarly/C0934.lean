import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0934 : checkSingleBlackFast (-12, 11) 7581 .east (2, -6) (-20, -21) = true := by
  decide +kernel

end LangtonsAnt
