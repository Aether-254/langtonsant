import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0252 : checkSingleBlackFast (11, 9) 5996 .north (-1, -5) (-19, -9) = true := by
  decide +kernel

end LangtonsAnt
