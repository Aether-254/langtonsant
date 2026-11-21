import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0275 : checkSingleBlackFast (15, 7) 5669 .west (-2, 4) (-16, -5) = true := by
  decide +kernel

end LangtonsAnt
