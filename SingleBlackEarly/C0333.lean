import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0333 : checkSingleBlackFast (3, 13) 11523 .west (-7, 7) (-24, -5) = true := by
  decide +kernel

end LangtonsAnt
