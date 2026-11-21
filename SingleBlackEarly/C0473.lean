import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0473 : checkSingleBlackFast (11, 15) 13468 .north (-1, 4) (-23, -24) = true := by
  decide +kernel

end LangtonsAnt
