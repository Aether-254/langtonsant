import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0188 : checkSingleBlackFast (10, -2) 23445 .east (10, 2) (-22, -15) = true := by
  decide +kernel

end LangtonsAnt
